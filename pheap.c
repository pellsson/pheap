#include "pheap.h"

#define pheap_static_assert(cond, name) \
    typedef char static_assertion_##name[(cond) ? 1 : -1];

//
// Make sure everything looks sane.
// These could be defined by user.
//
pheap_static_assert(sizeof(void *) == sizeof(size_t), bad_size_t);
pheap_static_assert(sizeof(uint8_t) == 1, bad_uint8_t);
pheap_static_assert(sizeof(uint16_t) == 2, bad_uint16_t);
pheap_static_assert(sizeof(uint32_t) == 4, bad_uint32_t);
pheap_static_assert(sizeof(uint64_t) == 8, bad_uint64_t);
pheap_static_assert(sizeof(uintptr_t) == sizeof(void *), bad_uintptr_t);
pheap_static_assert(sizeof(int8_t) == 1, bad_int8_t);
pheap_static_assert(sizeof(int16_t) == 2, bad_int16_t);
pheap_static_assert(sizeof(int32_t) == 4, bad_int32_t);
pheap_static_assert(sizeof(int64_t) == 8, bad_int64_t);
pheap_static_assert(sizeof(intptr_t) == sizeof(void *), bad_intptr_t);

pheap_static_assert(0 != PHEAP_ALIGNMENT, bad_alignment);

pheap_static_assert(PHEAP_MEMBLOCK_SIZE_HINT >= PHEAP_PAGE_SIZE, hint_too_small);

//
// Solve compiler and architecture
//
#ifdef _MSC_VER

    #include <intrin.h>

    #if defined(_WIN64)
        #define PHEAP_WIN
        typedef int64_t ssize_t;
    #elif defined(_WIN32)
        #define PHEAP_WIN
        typedef int32_t ssize_t;
    #else
        #error Cant resolve what we are building for (CL).
    #endif

    typedef volatile long pheap_internal_lock_t;

#if defined(_M_ARM) || defined(_M_ARM64)
    #define pheap_pause() __yield()
#else
    #define pheap_pause() _mm_pause()
#endif
    #define pheap_inline __forceinline
    #define pheap_trap() __debugbreak();
    #define pheap_atomic_testandset(ptr, bit) _interlockedbittestandset(ptr, bit)

    static uint32_t bitscan_forward32(uint32_t v)
    {
        uint32_t tmp;
        _BitScanForward((unsigned long *)&tmp, v);
        return tmp;
    }

#elif defined(__GNUC__)
    #include <sys/types.h> // ssize_t

    #if !defined(__x86__) && !defined(__x86_64__) && !defined(__arm__)
        #error Unknown architecture. Please fix :)
    #endif

    #if defined(__x86__) || defined(__x86_64__)
        #define pheap_trap() __asm__("int3")
        #define pheap_pause() __asm__("pause")
    #elif defined(__arm__)
        #define pheap_trap() __asm__("bkpt")
        #define pheap_pause() __asm__("yield")
    #else
        #error Cant resolve what we are building for (GCC-esk)
    #endif

    #if defined(__MINGW32__) || defined(_WIN32)
        #define PHEAP_WIN
    #else
        #define PHEAP_POSIX
    #endif

    typedef volatile uint32_t pheap_internal_lock_t;
    
    #define pheap_inline __attribute__((always_inline))
    #define bitscan_forward32(v) (uint32_t)__builtin_ctz((unsigned int)(v))

    pheap_inline static int pheap_atomic_testandset(volatile uint32_t *lock, uint32_t bit)
    {
        uint32_t carry = 0;
        asm("lock bts %2, %1;\n"
            "setc %0"
            : "+m" (carry), "=m" (*lock) : "r" (bit));
        return carry;
    }
#else
    #error Your compiler is not recognized.
    
    #define pheap_trap()    // Trap the processor
    #define pheap_inline    // Inline directive

    // Replace with opcode if present.
    static uint32_t bitscan_forward32(uint32_t v) 
    {
        uint32_t pos = 0;
        do
        {
            if(v & (1 << pos))
            {
                break;
            }
        }
        while(++pos);
        return pos;
    }
#endif

#if defined(PHEAP_WIN)
    #define WIN32_LEAN_AND_MEAN
    #include <windows.h>
    #ifndef pheap_yield
        #define pheap_yield() Sleep(0)
    #endif
#endif

#if PHEAP_NATIVE_ALLOC == 1
    #if defined(PHEAP_WIN)
    static void *pheap_native_alloc(size_t n, int exec)
    {
        DWORD prot = exec ? PAGE_EXECUTE_READWRITE : PAGE_READWRITE;
        return VirtualAlloc(PHEAP_NULL, n, MEM_COMMIT | MEM_RESERVE, prot);
    }

    static void pheap_native_destroy(void *p, size_t n)
    {
        (void)n;

        if(!VirtualFree(p, 0, MEM_RELEASE))
        {
            pheap_trap();
        }
    }
    #elif defined(PHEAP_POSIX)
    #include <sys/mman.h>
    
    #ifndef pheap_yield
        #include <unistd.h> // Probably kills osx?
        #define pheap_yield() sleep(0)
    #endif
    //
    // Assume everything but Windows has mmap()
    //
    static void *pheap_native_alloc(size_t n, int exec)
    {
        int prot = PROT_READ|PROT_WRITE;
        if(exec)
        {
            prot |= PROT_EXEC;
        }
        return mmap(0, n, prot, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    }
    static void pheap_native_destroy(void *p, size_t n)
    {
        if(0 != munmap(p, n))
        {
            pheap_trap();
        }
    }
    #else
        #error Unknown OS. No idea how to generate native allocation primitives.
    #endif
#else // !PHEAP_NATIVE_ALLOC
    void *pheap_native_alloc(size_t n, int exec);
    void pheap_native_destroy(void *p, size_t n);
#endif // PHEAP_NATIVE_ALLOC

#define pheap_is_exec(flags) (((flags) & PHEAP_FLAG_EXEC) ? 1 : 0)

#if PHEAP_LOCK_PRIMITIVE != PHEAP_NO_LOCK
    #define PHEAP_USE_LOCKS
#endif

#if PHEAP_LOCK_PRIMITIVE == PHEAP_PTHREAD_LOCK
    #include <pthread.h>
    typedef pthread_mutex_t pheap_lock_t;
    #define pheap_init_native_lock(lock)   pthread_mutex_init(lock, NULL)
    #define pheap_uninit_native_lock(lock) pthread_mutex_destroy(lock)
    #define pheap_lock_native_lock(lock)   pthread_mutex_lock(lock)
    #define pheap_unlock_native_lock(lock) pthread_mutex_unlock(lock)
#elif PHEAP_LOCK_PRIMITIVE == PHEAP_WIN32_LOCK
    #ifndef PHEAP_WIN
        #error You can only use win32 locking on Windows...
    #endif
    typedef CRITICAL_SECTION pheap_lock_t;
    #define pheap_init_native_lock(lock)   InitializeCriticalSection(lock)
    #define pheap_uninit_native_lock(lock) DeleteCriticalSection(lock)
    #define pheap_lock_native_lock(lock)   EnterCriticalSection(lock)
    #define pheap_unlock_native_lock(lock) LeaveCriticalSection(lock)
#elif PHEAP_LOCK_PRIMITIVE == PHEAP_INTERNAL_LOCK
    typedef pheap_internal_lock_t pheap_lock_t;
    #define pheap_init_native_lock(lock)   pheap_unlock_internal_lock(lock)
    #define pheap_uninit_native_lock(lock) // nothing to do
    #define pheap_lock_native_lock(lock)   pheap_lock_internal_lock(lock)
    #define pheap_unlock_native_lock(lock) pheap_unlock_internal_lock(lock)
#elif PHEAP_LOCK_PRIMITIVE == PHEAP_CUSTOM_LOCK
    void pheap_init_native_lock(pheap_lock_t *lock);
    void pheap_uninit_native_lock(pheap_lock_t *lock);
    void pheap_lock_native_lock(pheap_lock_t *lock);
    void pheap_unlock_native_lock(pheap_lock_t *lock);
#endif

// Internal heap flags
#define PHEAP_FLAG_FIXED    0x80000000
//
#define PHEAP_AFLAG_IN_USE  0x80
#define PHEAP_AFLAG_IS_HUGE 0x40

#define PHEAP_MAX_EXTRA_SIZE    0x3F
#define PHEAP_EXTRA_SIZE_MASK   ((uint32_t)(~(PHEAP_AFLAG_IN_USE|PHEAP_AFLAG_IS_HUGE)))

#define PHEAP_MAX_FREEBIN_SCANS 8

#define PHEAP_LIST_END ((void *)(~((uintptr_t)0)))

typedef uint8_t pheap_hash_t;

#define PHEAP_SIZE_BITS         (32)
#define PHEAP_NORMAL_SIZE_BITS  (PHEAP_SIZE_BITS-4)
#define PHEAP_MEMBLOCK_BUCKETS  (1<<sizeof(pheap_hash_t))
#define PHEAP_HUGE_SIZE_MASK    (~((((size_t)1) << ((size_t)PHEAP_NORMAL_SIZE_BITS)) - ((size_t)1)))
#define PHEAP_ALLOC_OBJ_SIZE    ((int32_t)pheap_roundup2(sizeof(pheap_allocation_free_t), PHEAP_ALIGNMENT))
#define PHEAP_FREE_DIFF         ((int32_t)(PHEAP_ALLOC_OBJ_SIZE - pheap_roundup2(sizeof(pheap_allocation_t), PHEAP_ALIGNMENT)))
#define PHEAP_PAGE_MASK         (~((size_t)(PHEAP_PAGE_SIZE - 1)))

#define pheap_roundup2(val, by) (((val) + ((by) - 1)) & (~((by) - 1)))

#define pheap_next_allocation(a)        (void *)(((uint8_t *)a) + get_full_alloc_size(a))
// TODO : I think this is wrong...?
#define pheap_search_dir_forward(n, s)  ((n > ((s) - (((s) - ((s) >> 1)) / 2))) ? 1 : 0)

#define pheap_obj_to_mem(a) \
    ((void *)(((uint8_t *)(a)) + pheap_roundup2(sizeof(pheap_allocation_t), PHEAP_ALIGNMENT)))
#define pheap_mem_to_obj(m) \
    ((pheap_allocation_t *)(((uint8_t *)(m)) - pheap_roundup2(sizeof(pheap_allocation_t), PHEAP_ALIGNMENT)))
#define pheap_obj_to_huge(a) \
    ((pheap_huge_allocation_t *)(((uint8_t *)(a)) - (sizeof(pheap_huge_allocation_t) - sizeof(pheap_allocation_t))))
#define pheap_huge_to_allocbase(huge) \
    ((void *)(((uintptr_t)huge) & PHEAP_PAGE_MASK))

typedef struct dlist
{
    struct dlist *next;
    struct dlist *prev;
}
dlist_t;

pheap_inline static void dlist_init(dlist_t *head)
{
    head->next = head->prev = head;
}

pheap_inline static int dlist_is_empty(const dlist_t *head)
{
    return head == head->next;
}

pheap_inline static void dlist_remove(dlist_t *entry)
{
    dlist_t *prev = entry->prev;
    dlist_t *next = entry->next;
    prev->next = next;
    next->prev = prev;
}

pheap_inline static void *dlist_remove_tail(dlist_t *head)
{
    dlist_t *ret = head->prev;
    dlist_remove(head);
    return ret;
}

pheap_inline static void *dlist_remove_head(dlist_t *head)
{
    dlist_t *ret = head->next;
    dlist_remove(head);
    return ret;
}

pheap_inline static void dlist_insert_head(dlist_t *head, dlist_t *entry)
{
    dlist_t *h = head;
    dlist_t *next = h->next;
    entry->next = next;
    entry->prev = h;
    h->next = entry;
    next->prev = entry;
}

pheap_inline static void dlist_insert_tail(dlist_t *head, dlist_t *entry)
{
    dlist_t *h = head;
    dlist_t *prev = h->prev;
    entry->next = h;
    entry->prev = prev;
    prev->next = entry;
    h->prev = entry;
}

#define dlist_to_type(obj, type, field) \
    ((type *)(((uint8_t *)obj) - ((uintptr_t)(&((type *)0)->field))))

#pragma pack(push, 1)

typedef struct pheap_allocation
{
    struct pheap_allocation *prev;
    // When allocated, requested allocation size
    // When free, size of entire allocation block including header.
    int32_t size;
    pheap_hash_t mem_bucket;
    // Holds flag as well as:
    // When allocated, add this with size to get allocation size
    // When free, always zero
    uint8_t extra;
}
pheap_allocation_t;

typedef struct pheap_huge_allocation
{
    dlist_t list;
    size_t huge_size;
    pheap_allocation_t allocation;
}
pheap_huge_allocation_t;

pheap_static_assert(sizeof(pheap_huge_allocation_t) <= PHEAP_PAGE_SIZE, page_size_too_small);

typedef struct pheap_allocation_free
{
    pheap_allocation_t allocation;
    dlist_t free_list;
}
pheap_allocation_free_t;

#pragma pack(pop)

typedef struct pheap_memblock
{
    dlist_t list; // must be first
    dlist_t hash_list;
    struct pheap_allocation *prev_alloc;
    ssize_t total_size;
    ssize_t bytes_left;
    uint8_t *unused;
}
pheap_memblock_t;

struct pheap
{
    uint64_t flags;
#ifdef PHEAP_USE_LOCKS
    pheap_lock_t lock;
#endif
    dlist_t huge_list;
    dlist_t mem_list;
    dlist_t mem_buckets[PHEAP_MEMBLOCK_BUCKETS];
    dlist_t free_list[PHEAP_SIZE_BITS];
};

pheap_static_assert((PHEAP_ALLOC_OBJ_SIZE * 2) <= (PHEAP_EXTRA_SIZE_MASK + 1), object_too_big);

pheap_inline static void pheap_lock_internal_lock(pheap_internal_lock_t *lock)
{
    while(pheap_atomic_testandset(lock, 1))
    {
#ifdef pheap_yield
        pheap_yield();
#else
        pheap_pause();
#endif
    }
}

pheap_inline static void pheap_unlock_internal_lock(pheap_internal_lock_t *lock)
{
    *lock = 0;
}

pheap_inline static void pheap_init_lock(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_init_native_lock(&h->lock);
    }
}

pheap_inline static void pheap_uninit_lock(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_uninit_native_lock(&h->lock);
    }   
}

pheap_inline static void pheap_lock(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_lock_native_lock(&h->lock);
    }
}

pheap_inline static void pheap_unlock(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_unlock_native_lock(&h->lock);
    }
}

static pheap_inline pheap_hash_t hash_pointer(const void *p)
{
    return (pheap_hash_t)(((uintptr_t)p) / PHEAP_MEMBLOCK_SIZE_HINT);
}

#if PHEAP_INTERNAL_DEBUG == 1
    #include <stdio.h>
    #include <stdlib.h>
    #define pheap_impossible(...) \
        printf("IMPOSSIBLE: " __VA_ARGS__); \
        fflush(stdout); \
        pheap_trap()
    #define pheap_assert(x, s) \
        if(!(x)) \
        { \
            pheap_impossible("ASSERTION_FAIL: " s); \
        }
#else
    #define pheap_impossible(s) pheap_trap()
    #define pheap_assert(x, s)
#endif

pheap_inline static void set_allocated_size(pheap_allocation_t *a, int32_t size, int32_t alloc_size)
{
    pheap_assert(size < alloc_size, "Size is smaller than allocation size...");
    pheap_assert((alloc_size - size) <= PHEAP_MAX_EXTRA_SIZE,
        "Size expands into flags, something is very wrong");

    a->size = size;
    a->extra = (uint8_t)((alloc_size - size) | PHEAP_AFLAG_IN_USE);
}

pheap_inline static uint32_t size_to_index(int32_t nv, int32_t *bucket_upper_bound)
{
    uint32_t n = (uint32_t)nv;
    n--;
    n |= n >> 1;
    n |= n >> 2;
    n |= n >> 4;
    n |= n >> 8;
    n |= n >> 16;
    n++;
    if(bucket_upper_bound)
    {
        *bucket_upper_bound = (int32_t)n;
    }
    return bitscan_forward32(n);
}

pheap_inline static void unlink_free(void *ptr)
{
    pheap_allocation_free_t *f = (pheap_allocation_free_t *)ptr;
    dlist_remove(&f->free_list);
}

pheap_inline static void make_free(void *a)
{
    pheap_allocation_free_t *f = a;

    pheap_assert(0 == (f->allocation.extra & PHEAP_AFLAG_IS_HUGE),
        "Huge pages should never be here.");

    if(f->allocation.extra & PHEAP_AFLAG_IN_USE)
    {
        f->allocation.size += f->allocation.extra & PHEAP_EXTRA_SIZE_MASK;
        f->allocation.extra = 0;
    }
}

pheap_inline static int32_t get_full_alloc_size(const pheap_allocation_t *a)
{
    return a->size + (a->extra & PHEAP_EXTRA_SIZE_MASK);
}

pheap_inline static void merge_free(void *keep, void *merge)
{
    pheap_allocation_free_t *k = keep;
    pheap_allocation_free_t *m = merge;

    make_free(keep);
    make_free(merge);

    k->allocation.size += get_full_alloc_size(&m->allocation);
}

pheap_inline static void release_allocation(pheap_t h, void *a)
{
    int32_t bucket_upper_bound;
    pheap_allocation_free_t *f = a;
    dlist_t *list;

    make_free(a);

    list = (h->free_list + size_to_index(f->allocation.size, &bucket_upper_bound));

    if(pheap_search_dir_forward(f->allocation.size, bucket_upper_bound))
    {
        //
        // Push to head
        //
        dlist_insert_head(list, &f->free_list);
    }
    else
    {
        //
        // Push to tail
        //
        dlist_insert_tail(list, &f->free_list);
    }
}

pheap_inline static void take_memblock_bytes(pheap_memblock_t *mem, int32_t size)
{
    mem->bytes_left -= size;
    mem->unused += size;
    *((void **)mem->unused) = PHEAP_LIST_END;
}

pheap_inline static int memblock_can_alloc(const pheap_memblock_t *mem, int32_t alloc_size)
{
    return mem->bytes_left >= ((ssize_t)alloc_size + (ssize_t)sizeof(PHEAP_LIST_END));
}

pheap_inline static pheap_allocation_t *unchecked_allocate(pheap_memblock_t *mem, int32_t size, int32_t alloc_size)
{
    pheap_allocation_t *a = (pheap_allocation_t *)mem->unused;

    take_memblock_bytes(mem, alloc_size);
    a->prev = mem->prev_alloc;
    set_allocated_size(a, size, alloc_size);
    a->mem_bucket = (hash_pointer(mem) % PHEAP_MEMBLOCK_BUCKETS);

    mem->prev_alloc = a;

    return a;
}

pheap_inline static pheap_allocation_t *allocate_from_existing(pheap_t h, int32_t size, int32_t alloc_size)
{
    pheap_allocation_t *a = PHEAP_NULL;
    dlist_t *next;

    for(next = h->mem_list.next; next != &h->mem_list; next = next->next)
    {
        pheap_memblock_t *mem = (pheap_memblock_t *)next;

        if(memblock_can_alloc(mem, alloc_size))
        {
            a = unchecked_allocate(mem, size, alloc_size);
            break;
        }
    }
    
    return a;   
}

pheap_inline static pheap_memblock_t *find_memblock(pheap_t h, const pheap_allocation_t *a)
{
    dlist_t *head = h->mem_buckets + a->mem_bucket;
    const uint8_t *ptr = (const uint8_t *)a; 

    for(dlist_t *it = head->next; it != head; it = it->next)
    {
        const pheap_memblock_t *mem = dlist_to_type(it, pheap_memblock_t, hash_list);
        const uint8_t *start = ((const uint8_t *)mem) + pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT);
        const uint8_t *end = start + mem->total_size;

        if(ptr >= start && ptr < end)
        {
            return (pheap_memblock_t *)mem;
        }
    }

    pheap_impossible("Unable to locate memblock from which data was freed (everything broken)\n");
    return PHEAP_NULL;
}

pheap_inline static void memblock_init(pheap_t h, pheap_memblock_t *mem, size_t alloced)
{
    uint32_t hash_bucket = (hash_pointer(mem) % PHEAP_MEMBLOCK_BUCKETS);

    dlist_insert_head(&h->mem_list, &mem->list);
    dlist_insert_head(&h->mem_buckets[hash_bucket], &mem->hash_list);

    mem->prev_alloc = 0;
    mem->total_size = alloced - pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT);
    mem->bytes_left = alloced - pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT);
    mem->unused = ((uint8_t *)mem) + pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT);
}

pheap_inline static int32_t required_alloc_size(int32_t size)
{
    if(size < PHEAP_FREE_DIFF)
    {
        return PHEAP_ALLOC_OBJ_SIZE;
    }
    return pheap_roundup2(PHEAP_ALLOC_OBJ_SIZE + size, PHEAP_ALIGNMENT) - PHEAP_FREE_DIFF;
}

pheap_inline static pheap_allocation_t *create_allocation(pheap_t h, int32_t size)
{
    ssize_t alloc_size;
    pheap_memblock_t *mem;
    pheap_allocation_t *a = PHEAP_NULL;
    int32_t req_size = required_alloc_size(size);

    if(h->flags & PHEAP_FLAG_FIXED)
    {
        return PHEAP_NULL;
    }

    if(PHEAP_NULL != (a = allocate_from_existing(h, size, req_size)))
    {
        return a;
    }
    //
    // No more bytes, allocate another block
    //
    alloc_size = ((ssize_t)pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT)) + (ssize_t)(req_size * 2);

    if(alloc_size < req_size)
    {
        // Too large.
        return PHEAP_NULL;
    }

    if(alloc_size < PHEAP_MEMBLOCK_SIZE_HINT)
    {
        alloc_size = PHEAP_MEMBLOCK_SIZE_HINT;
    }
    else
    {
        alloc_size = pheap_roundup2(alloc_size, PHEAP_MEMBLOCK_SIZE_HINT);
    }

    pheap_unlock(h);
    mem = pheap_native_alloc(alloc_size, pheap_is_exec(h->flags));
    pheap_lock(h);

    if(PHEAP_NULL != mem)
    {
        memblock_init(h, mem, alloc_size);
        a = unchecked_allocate(mem, size, req_size);
    }

    return a;
}

static void release_to_memblock_end(pheap_t h, pheap_allocation_t *prev, void *a)
{
    pheap_memblock_t *mem;
    int32_t asize = get_full_alloc_size(a);
#if PHEAP_INTERNAL_DEBUG == 1
    pheap_allocation_t *next = (pheap_allocation_t *)(((uint8_t *)a) + asize);
    pheap_assert(PHEAP_LIST_END == next->prev, "Impossible release?");
#endif
    mem = find_memblock(h, a);
    mem->bytes_left += asize;

    //if(mem->next_slist != NULL && (mem->total_size == mem->bytes_left))
    //{
    //    pheap_memblock_t *prev = NULL;
    //    pheap_memblock_t *curr;
    //    //
    //    // Release the block.
    //    // Not thrilled about this, should probably make it a double-list...
    //    //
    //    for(curr = h->mem_list; curr; curr = curr->next_slist)
    //    {
    //        if(curr == mem)
    //        {
    //            

    //            prev->next_slist = curr->next_slist;
    //            pheap_unlock(h);

    //            pheap_native_destroy(mem, mem->total_size + pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT));

    //            pheap_lock(h);
    //            return;
    //        }

    //        prev = curr;
    //    }
    //}

    mem->unused -= asize;
    mem->prev_alloc = prev;

    *((void **)mem->unused) = PHEAP_LIST_END;
}

static void merge_with_right(void *left, void *right)
{
    pheap_allocation_t *next;

    pheap_assert(!(((pheap_allocation_t *)right)->extra & PHEAP_AFLAG_IN_USE), "Cant merge right with used block");

    unlink_free(right);
    merge_free(left, right);

    next = pheap_next_allocation(left);
    pheap_assert(next->extra & PHEAP_AFLAG_IN_USE, 
        "Object following end-merge is not in use, this should be impossible.\n");
    pheap_assert(next->prev != PHEAP_LIST_END,
        "This must be possible? Wont that break everything??");
    next->prev = left;
}

pheap_inline static void shrink_and_split(pheap_t h, void *obj, int32_t want_size, int32_t full_size)
{
    pheap_allocation_t *a = obj;
    pheap_allocation_t *next;

    int32_t req_size = required_alloc_size(want_size);
    int32_t split_size = (full_size - req_size);

#if PHEAP_INTERNAL_DEBUG == 1
    int already_alloced = a->extra & PHEAP_AFLAG_IN_USE;
#endif

    pheap_assert(split_size >= 0, "Cant increase the size of an allocation like that.");

    if(split_size >= PHEAP_ALLOC_OBJ_SIZE)
    {
        pheap_allocation_free_t *split;

        next = pheap_next_allocation(a);

        set_allocated_size(a, want_size, req_size);
        split = pheap_next_allocation(a);
        split->allocation.prev = a;
        split->allocation.size = split_size;
        split->allocation.extra = 0;
        split->allocation.mem_bucket = a->mem_bucket;
        //
        // [realloc_ptr] [this split] [END] => [realloc_ptr] [END]
        //
        if(PHEAP_LIST_END == next->prev)
        {
            pheap_assert(already_alloced, "A free block must not reside next to end. (splitting).");
            release_to_memblock_end(h, a, split);

            return;
        }
        //
        // If the block following the original block is free, merge the split one and the one after.
        //
        if(!(next->extra & PHEAP_AFLAG_IN_USE))
        {
            //
            // [realloc_ptr] [this split] [FREE] [???] => [realloc_ptr] [???]
            //
            pheap_assert(already_alloced, "A free block must not reside next to end. (merge).");
            unlink_free(next);
            split->allocation.size += next->size;
        }

        next = pheap_next_allocation(&split->allocation);

        if(PHEAP_LIST_END == next->prev)
        {
            //
            // [realloc_ptr] [this split] [FREE] [END] => [realloc_ptr] [END]
            //
            pheap_assert(already_alloced, "A free block must not reside next to end. (splitting).");
            release_to_memblock_end(h, a, split);

            return;
        }
        //
        // [realloc_ptr] [this split] [FREE] [alloced] => [realloc_ptr] [alloced]
        //
        pheap_assert(next->extra & PHEAP_AFLAG_IN_USE, "Object not in use nor end.");

        next->prev = &split->allocation;
        release_allocation(h, split);
    }
    else
    {
        set_allocated_size(a, want_size, req_size);
        pheap_assert(((uint32_t)(a->extra & PHEAP_EXTRA_SIZE_MASK)) + ((uint32_t)(full_size - req_size)) 
                        <= PHEAP_MAX_EXTRA_SIZE, "Impossible diff? Extra has grown too large");
        a->extra += (uint8_t)(full_size - req_size);      
        next = pheap_next_allocation(a);
        if(PHEAP_LIST_END != next->prev)
        {
            next->prev = a;
        }
        else
        {
            pheap_assert(already_alloced, "Free next to tail?");
            pheap_assert(a == find_memblock(h, a)->prev_alloc, "Impossible prev_alloc state.");
        }
    }
}

static pheap_allocation_t *claim_free_bin(pheap_t h, pheap_allocation_free_t *f, int32_t size)
{
    unlink_free(f);
    shrink_and_split(h, &f->allocation, size, f->allocation.size);
    return &f->allocation;
}

static pheap_allocation_t *allocate_from_free_bin(pheap_t h, int32_t size)
{
    int32_t req_size = required_alloc_size(size);

    uint32_t i = 0;
    int32_t upper;
    uint32_t free_buckets;

    uint32_t index = size_to_index(req_size, &upper);
    dlist_t *list = (h->free_list + index);

    int search_fwd = pheap_search_dir_forward(req_size, upper);

    dlist_t *it = (search_fwd ? list->next : list->prev);

    while(it != list)
    {
        pheap_allocation_free_t *f = dlist_to_type(it, pheap_allocation_free_t, free_list);

        if(f->allocation.size >= req_size)
        {
            return claim_free_bin(h, f, size);
        }

        if(++i >= PHEAP_MAX_FREEBIN_SCANS)
        {
            //
            // Taking too long, look in bigger bins instead
            // TODO XXX - If we are searching backwards, maybe check head? Likely a big allocation there.
            //
            break;
        }
        
        if(search_fwd)
        {
            it = it->next;
        }
        else
        {
            it = it->prev;
        }
    }

    free_buckets = PHEAP_NORMAL_SIZE_BITS;
    if(h->flags & PHEAP_FLAG_FIXED)
    {
        //
        // In fixed-mode, there are no huge pages and all buckets are used for the heap.
        //
        free_buckets = PHEAP_SIZE_BITS;
    }

    for(i = (index + 1); i < free_buckets; ++i)
    {
        list = (h->free_list + i);
        if(list != list->prev)
        {
            pheap_allocation_free_t *f = dlist_to_type(list->prev, pheap_allocation_free_t, free_list);
            return claim_free_bin(h, f, size);
        }
    }

    return PHEAP_NULL;
}

pheap_inline static void link_huge_alloc(pheap_t h, pheap_huge_allocation_t *a)
{
    pheap_lock(h);
    dlist_insert_head(&h->huge_list, &a->list);
    pheap_unlock(h);
}

pheap_inline static void unlink_huge_alloc(pheap_t h, pheap_huge_allocation_t *a)
{
    pheap_lock(h);
    dlist_remove(&a->list);
    pheap_unlock(h);
}

void *pheap_alloc(pheap_t h, size_t n)
{
    pheap_allocation_t *a;

    if(!(h->flags & PHEAP_FLAG_FIXED))
    {
        if((n & PHEAP_HUGE_SIZE_MASK) || ((n + PHEAP_ALLOC_OBJ_SIZE) & PHEAP_HUGE_SIZE_MASK))
        {
            uint8_t *ptr;
            pheap_huge_allocation_t *huge;
            size_t rounded = pheap_roundup2(n, PHEAP_PAGE_SIZE);

            if(rounded < n)
            {
                return PHEAP_NULL;
            }
            if(PHEAP_NULL == (ptr = pheap_native_alloc(rounded + PHEAP_PAGE_SIZE, pheap_is_exec(h->flags))))
            {
                return PHEAP_NULL;
            }

            a = pheap_mem_to_obj(ptr + PHEAP_PAGE_SIZE);

            huge = pheap_obj_to_huge(a);
            huge->huge_size = n;

            huge->allocation.size = 0;
            huge->allocation.prev = PHEAP_NULL;
            huge->allocation.extra = PHEAP_AFLAG_IN_USE | PHEAP_AFLAG_IS_HUGE;
            huge->allocation.mem_bucket = 0;
            
            link_huge_alloc(h, huge);
            return (ptr + PHEAP_PAGE_SIZE);
        }
    }
    else if(n >= 0xFFFFFF00)
    {
        //
        // Due to the internal allocation structures only huge-allocs can be >32-bits.
        // This puts a 32-bit limitation on PHEAP_FLAG_FIXED that cant allocate huge pages.
        //
        return PHEAP_NULL;
    }

    pheap_lock(h);

    if(PHEAP_NULL != (a = allocate_from_free_bin(h, (uint32_t)n)))
    {
        pheap_unlock(h);
        return pheap_obj_to_mem(a);
    }

    if(PHEAP_NULL == (a = create_allocation(h, (uint32_t)n)))
    {
        pheap_unlock(h);
        return PHEAP_NULL;
    }

    pheap_unlock(h);
    return pheap_obj_to_mem(a);
}

void *pheap_zalloc(pheap_t h, size_t n)
{
    void *ptr = pheap_alloc(h, n);
    if(PHEAP_NULL != ptr)
    {
        pheap_memset(ptr, 0, n);
    }

    return ptr;
}

static void *simple_realloc(pheap_t h, void *old, size_t n)
{
    void *ptr;
    size_t old_size = pheap_msize(old);
    //
    // TODO XXX Wouldnt it be safe to call free() here and then potentially reuse the memory
    //          it currently resides in partially? Or can the data get overwritten? Naaah?
    //          Will consider when I am less tired :)
    //
    if(PHEAP_NULL == (ptr = pheap_alloc(h, n)))
    {
        return PHEAP_NULL;
    }

    pheap_memcpy(ptr, old, (n < old_size) ? n : old_size);
    pheap_free(h, old);

    return ptr;
}

void *pheap_realloc(pheap_t h, void *p, size_t n)
{
    pheap_allocation_t *curr;
    int32_t old_full;
    size_t old_size;

    if(PHEAP_NULL == p)
    {
        return pheap_alloc(h, n);
    }

    old_size = pheap_msize(p);

    if(!(h->flags & PHEAP_FLAG_FIXED))
    {
        if((n & PHEAP_HUGE_SIZE_MASK) || ((n + PHEAP_ALLOC_OBJ_SIZE) & PHEAP_HUGE_SIZE_MASK))
        {
            return simple_realloc(h, p, n);
        }
    }
    else if(n >= 0xFFFFFF00)
    {
        //
        // Due to the internal allocation structures only huge-allocs can be >32-bits.
        // This puts a 32-bit limitation on PHEAP_FLAG_FIXED that cant allocate huge pages.
        //
        return PHEAP_NULL;
    }

    curr = pheap_mem_to_obj(p);

    if(curr->extra & PHEAP_AFLAG_IS_HUGE)
    {
        return simple_realloc(h, p, n);
    }

    old_full = get_full_alloc_size(curr);

    if(n < old_size)
    {
        //
        // Allocation is smaller
        //
        pheap_lock(h);
        shrink_and_split(h, curr, (int32_t)n, old_full);
        pheap_unlock(h);

        return p;
    }
    else if(n > old_size)
    {
        int32_t avail;
        int32_t req_size = required_alloc_size((int32_t)n);      
        pheap_allocation_t *next;

        pheap_lock(h);
        
        next = pheap_next_allocation(curr);

        if(next->prev == PHEAP_LIST_END)
        {
            //
            // Allocation is at the end of its memory block,
            // see if there are bytes left to increase the allocation...
            //
            int32_t diff = (int32_t)(n - old_size);
            pheap_memblock_t *mb = find_memblock(h, curr);
            if(memblock_can_alloc(mb, diff))
            {
                take_memblock_bytes(mb, diff);
                curr->size += diff;
            }
            else
            {
                pheap_unlock(h);
                return simple_realloc(h, p, n);
            }

            pheap_unlock(h);
            return p;
        }
 
        if(next->extra & PHEAP_AFLAG_IN_USE)
        {
            pheap_unlock(h);
            return simple_realloc(h, p, n);
        }

        avail = old_full + get_full_alloc_size(next);

        if(avail < req_size)
        {
            pheap_unlock(h);
            return simple_realloc(h, p, n);
        }
        //
        // If we combine this allocation with the block after it, we have enough bytes
        // to satisfy the requested size.
        //
        merge_with_right(curr, next);
        shrink_and_split(h, curr, (int32_t)n, avail);
        pheap_unlock(h);

        return p;
    }
    //
    // Old and new size are the same, just return p
    //
    return p;
}

void pheap_free(pheap_t h, void *p)
{
    pheap_allocation_t *a = pheap_mem_to_obj(p);
    pheap_allocation_t *prev;
    pheap_allocation_t *next;

    if(!p)
    {
        return;
    }

    // todo assert fix and so on
    if(0 == (PHEAP_AFLAG_IN_USE & a->extra))
    {
        pheap_impossible("Object being free is not in use (or not a pheap allocation)\n");
    }
    else if(PHEAP_AFLAG_IS_HUGE & a->extra)
    {
        void *ptr;
        pheap_huge_allocation_t *huge = pheap_obj_to_huge(a);
        unlink_huge_alloc(h, huge);
        
        ptr = pheap_huge_to_allocbase(huge);
        pheap_native_destroy(ptr, huge->huge_size + PHEAP_PAGE_SIZE);

        return;
    }
    
    pheap_lock(h);

    //
    // If prev is valid and not in use, merge previous allocation with this one.
    //
    prev = a->prev;
    if(prev)
    {
        //
        // Are we at end?
        //
        if(PHEAP_LIST_END == prev)
        {
            release_to_memblock_end(h, prev, a);
            goto cleanup;
        }
        //
        // Either:
        // [FREE] [THIS] [????]
        // or:
        // [USED] [THIS] [????]
        //
        if(0 == (prev->extra & PHEAP_AFLAG_IN_USE))
        {
            //
            // [FREE] [THIS] ---> [THIS    ]
            // The block before this block is also free. Merge the two.
            //
            unlink_free(prev);
            merge_free(prev, a);

            a = prev;
            prev = a->prev;
        }
    }
    //
    // Always:
    // [PREV/NULL] [THIS     ] ---> [????]; resolve [????]
    //
    next = pheap_next_allocation(a);

    if(PHEAP_LIST_END == next->prev)
    {
        //
        // It is [PREV/NULL] [THIS] ---> [END]
        // Change to [PREV/NULL] [END]
        //
        release_to_memblock_end(h, prev, a);
        goto cleanup;
    }
    else if(0 == (PHEAP_AFLAG_IN_USE & next->extra))
    {
        merge_with_right(a, next);
    }
    else
    {
        next->prev = a;
    }
    //
    // Set this free.
    //
    release_allocation(h, a);
cleanup:
    pheap_unlock(h);
}

size_t pheap_msize(const void *p)
{
    const pheap_allocation_t *a = pheap_mem_to_obj(p);
    if(PHEAP_AFLAG_IS_HUGE & a->extra)
    {
        return pheap_obj_to_huge(a)->huge_size;
    }
    return a->size;
}

static pheap_inline pheap_t init_pheap(void *ptr, size_t n, uint32_t flags)
{
    pheap_t h = ptr;
    pheap_memblock_t *mb;

    pheap_memset(h, 0, sizeof(*h));

    dlist_init(&h->huge_list);
    dlist_init(&h->mem_list);

    for(int i = 0; i < PHEAP_MEMBLOCK_BUCKETS; ++i)
    {
        dlist_init(h->mem_buckets + i);
    }

    for(int i = 0; i < PHEAP_SIZE_BITS; ++i)
    {
        dlist_init(h->free_list + i);
    }

    h->flags = flags;
    pheap_init_lock(h);

    mb = (pheap_memblock_t *)(((uint8_t *)ptr) + pheap_roundup2(sizeof(*h), PHEAP_ALIGNMENT));
    memblock_init(h, mb, n - pheap_roundup2(sizeof(*h), PHEAP_ALIGNMENT));

    return h;
}

pheap_t pheap_create_fixed(void *memory, size_t size, uint32_t flags)
{
    pheap_t h;
    pheap_memblock_t *mb;

    size_t min_size = pheap_roundup2(sizeof(*h), PHEAP_ALIGNMENT) 
                    + pheap_roundup2(sizeof(*mb), PHEAP_ALIGNMENT);

    if(size < min_size)
    {
        // Too small to host control structures
        return PHEAP_NULL;
    }
    if(flags & PHEAP_FLAG_EXEC)
    {
        // Missleading if set. The protection is whatever you set the memory to be.
        return PHEAP_NULL;
    }

    return init_pheap(memory, size, flags | PHEAP_FLAG_FIXED);
}

pheap_t pheap_create(uint32_t flags)
{
    void *ptr;
    size_t size = PHEAP_MEMBLOCK_SIZE_HINT;

    if(0 == (ptr = pheap_native_alloc(size, pheap_is_exec(flags))))
    {
        // 
        return PHEAP_NULL;
    }

    return init_pheap(ptr, size, flags & ~PHEAP_FLAG_FIXED);
}

void pheap_destory(pheap_t h)
{
    pheap_uninit_lock(h);

    if(h->flags & PHEAP_FLAG_FIXED)
    {
        return;
    }

    for(dlist_t *it = h->huge_list.next; it != &h->huge_list;)
    {
        dlist_t *next = it->next;
        pheap_huge_allocation_t *huge = (pheap_huge_allocation_t *)it;
        pheap_native_destroy(pheap_huge_to_allocbase(huge), huge->huge_size + PHEAP_PAGE_SIZE);
        it = next;
    }

    for(dlist_t *it = h->mem_list.next; it != &h->mem_list;)
    {
        pheap_memblock_t *mb = (pheap_memblock_t *)it;
        ssize_t n = mb->total_size + pheap_roundup2(sizeof(*mb), PHEAP_ALIGNMENT);
        dlist_t *next = it->next;
        //
        // The first allocated memory block (ie the last in this list), also hosts the pheap_t structure.
        //
        if(it == h->mem_list.prev)
        {
            //
            // Destroy the heap and exit.
            //
            pheap_native_destroy(h, n + pheap_roundup2(sizeof(*h), PHEAP_ALIGNMENT));
            break;
        }
        else
        {
            pheap_native_destroy(mb, n);
        }

        it = next;
    }
}

#if PHEAP_USE_GLOBAL_HEAP != 0

static pheap_internal_lock_t g_init_lock = 0;
static volatile pheap_t g_pheap = PHEAP_NULL;

pheap_inline static int pheap_global_init(void)
{
    if(PHEAP_NULL == g_pheap)
    {
        uint32_t flags = 0;
#if PHEAP_LOCK_PRIMITIVE != PHEAP_NO_LOCK
        flags = PHEAP_FLAG_THREADSAFE;
        pheap_lock_internal_lock(&g_init_lock);
#endif
        if(PHEAP_NULL == g_pheap)
        {
            g_pheap = pheap_create(flags);
            if(PHEAP_NULL == g_pheap)
            {
                pheap_trap();
                return 0;
            }
        }
#if PHEAP_LOCK_PRIMITIVE != PHEAP_NO_LOCK
        pheap_unlock_internal_lock(&g_init_lock);
#endif
    }
    return 1;
}

void *pheap_g_alloc(size_t n)
{
    if(!pheap_global_init())
    {
        return PHEAP_NULL;
    }
    return pheap_alloc(g_pheap, n);
}

void *pheap_g_zalloc(size_t n)
{
    if(!pheap_global_init())
    {
        return PHEAP_NULL;
    }
    return pheap_zalloc(g_pheap, n);
}

void *pheap_g_realloc(void *p, size_t n)
{
    if(!pheap_global_init())
    {
        return PHEAP_NULL;
    }
    return pheap_realloc(g_pheap, p, n);
}

void pheap_g_free(void *p)
{
    // If the first thing you do is call free the crash is on you...
    pheap_free(g_pheap, p);
}

#endif

#ifdef PHEAP_TEST

int pheap_test_is_pristine(pheap_t h)
{
    if(!dlist_is_empty(&h->huge_list))
    {
        return 0;
    }

    for(dlist_t *it = h->mem_list.next; it != &h->mem_list; it = it->next)
    {
        pheap_memblock_t *mb = (pheap_memblock_t *)it;

        if(mb->bytes_left != mb->total_size)
        {
            return 0;
        }
    }

    for(int i = 0; i < PHEAP_SIZE_BITS; ++i)
    {
        if(!dlist_is_empty(h->free_list + i))
        {
            return 0;
        }
    }

    return 1;
}

#endif // PHEAP_TEST

