#include "pheap.h"

#define PHEAP_NULL ((void *)0)

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
        typedef int64_t pheap_size_t;
    #elif defined(_WIN32)
        #define PHEAP_WIN
        typedef int32_t pheap_size_t;
    #else
        #error Cant resolve what we are building for (CL).
    #endif

    typedef volatile long pheap_internal_lock_t;

    #pragma warning(push)
    #pragma warning(disable: 4366) // warning C4366: The result of the unary '&' operator may be unaligned

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

    #if defined(__x86_64__) || defined(__aarch64__)
        typedef int64_t pheap_size_t;
    #elif defined(__i386__) || defined(__arm__)
        typedef int32_t pheap_size_t;
    #else
        #error Unknown architecture. Please fix :)
    #endif


    #if defined(__i386__) || defined(__x86_64__)
        #define pheap_trap() __asm__("int3")
        #define pheap_pause() __asm__("pause")
    #elif defined(__arm__) || defined(__aarch64__)
        #define pheap_trap() __builtin_trap()
        #define pheap_pause() __asm__ __volatile__("yield")
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

    #if defined(__i386__) || defined(__x86_64__)
    pheap_inline static int pheap_atomic_testandset(volatile uint32_t *lock, uint32_t bit)
    {
        uint32_t carry = 0;
        asm("lock bts %2, %1;\n"
            "setc %0"
            : "+m" (carry), "=m" (*lock) : "r" (bit));
        return carry;
    }
    #else
    // Portable implementation using GCC builtins for ARM and other architectures
    pheap_inline static int pheap_atomic_testandset(volatile uint32_t *lock, uint32_t bit)
    {
        uint32_t mask = 1u << bit;
        uint32_t old = __atomic_fetch_or(lock, mask, __ATOMIC_ACQUIRE);
        return (old & mask) ? 1 : 0;
    }
    #endif
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

#if PHEAP_SYSTEM_ALLOC == 1 && defined(PHEAP_WIN)
    #define WIN32_LEAN_AND_MEAN
    #include <windows.h>
    #ifndef pheap_yield
        #define pheap_yield() Sleep(0)
    #endif
#endif

#if PHEAP_SYSTEM_ALLOC == 1
    #if defined(PHEAP_WIN)
    static void *pheap_system_alloc(size_t n, int exec)
    {
        DWORD prot = exec ? PAGE_EXECUTE_READWRITE : PAGE_READWRITE;
        return VirtualAlloc(PHEAP_NULL, n, MEM_COMMIT | MEM_RESERVE, prot);
    }

    static void pheap_system_free(void *p, size_t n)
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
        #include <sched.h>
        #define pheap_yield() sched_yield()
    #endif
    //
    // Assume everything but Windows has mmap()
    //
    static void *pheap_system_alloc(size_t n, int exec)
    {
        int prot = PROT_READ|PROT_WRITE;
        if(exec)
        {
            prot |= PROT_EXEC;
        }
        return mmap(0, n, prot, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
    }
    static void pheap_system_free(void *p, size_t n)
    {
        if(0 != munmap(p, n))
        {
            pheap_trap();
        }
    }
    #else
        #error Unknown OS. No idea how to generate native allocation primitives.
    #endif
#endif // PHEAP_SYSTEM_ALLOC

#define pheap_is_exec(flags) (((flags) & PHEAP_FLAG_EXEC) ? 1 : 0)

#if PHEAP_HAS_LOCKS
    #define PHEAP_USE_LOCKS
#endif

#if PHEAP_LOCK_PRIMITIVE == PHEAP_PTHREAD_LOCK
    #include <pthread.h>
    typedef pthread_mutex_t pheap_lock_t;
    #define pheap_lock_init(lock)   pthread_mutex_init(lock, NULL)
    #define pheap_lock_destroy(lock) pthread_mutex_destroy(lock)
    #define pheap_lock_acquire(lock)   pthread_mutex_lock(lock)
    #define pheap_lock_release(lock) pthread_mutex_unlock(lock)
#elif PHEAP_LOCK_PRIMITIVE == PHEAP_WIN32_LOCK
    #ifndef PHEAP_WIN
        #error You can only use win32 locking on Windows...
    #endif
    typedef CRITICAL_SECTION pheap_lock_t;
    #define pheap_lock_init(lock)   InitializeCriticalSection(lock)
    #define pheap_lock_destroy(lock) DeleteCriticalSection(lock)
    #define pheap_lock_acquire(lock)   EnterCriticalSection(lock)
    #define pheap_lock_release(lock) LeaveCriticalSection(lock)
#elif PHEAP_LOCK_PRIMITIVE == PHEAP_INTERNAL_LOCK
    typedef pheap_internal_lock_t pheap_lock_t;
    #define pheap_lock_init(lock)   unlock_internal_lock(lock)
    #define pheap_lock_destroy(lock) // nothing to do
    #define pheap_lock_acquire(lock)   lock_internal_lock(lock)
    #define pheap_lock_release(lock) unlock_internal_lock(lock)
#endif

// Internal heap flags
#define PHEAP_FLAG_FIXED    0x80000000
//
#define PHEAP_AFLAG_IN_USE  0x80
#define PHEAP_AFLAG_IS_HUGE 0x40

#define PHEAP_MAX_EXTRA_SIZE    0x3F
#define PHEAP_EXTRA_SIZE_MASK   ((uint32_t)(~(PHEAP_AFLAG_IN_USE|PHEAP_AFLAG_IS_HUGE)))

#define PHEAP_MAX_FREEBIN_SCANS 8

#define PHEAP_LIST_END          (~((uint32_t)0))
#define PHEAP_LIST_END_ALLOC    ((pheap_allocation_t *)(~((uintptr_t)0)))

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
//
// Determines search direction within a free bin.
// Each free bin covers sizes [2^k, 2^(k+1)-1]. The bucket_upper_bound (s) is 2^(k+1).
// This macro simplifies to: n > (s - s/4) = n > (3s/4)
// Returns 1 (search forward/head-to-tail) if n is in the upper quarter of the bucket,
// meaning we want larger blocks first. Returns 0 (search backward/tail-to-head) if n
// is in the lower 3/4, searching for smaller blocks to reduce fragmentation.
//
#define pheap_search_dir_forward(n, s)  ((n > ((s) - (((s) - ((s) >> 1)) / 2))) ? 1 : 0)

#define pheap_obj_to_mem(a) \
    ((void *)(((uint8_t *)(a)) + pheap_roundup2(sizeof(pheap_allocation_t), PHEAP_ALIGNMENT)))
#define pheap_mem_to_obj(m) \
    ((pheap_allocation_t *)(((uint8_t *)(m)) - pheap_roundup2(sizeof(pheap_allocation_t), PHEAP_ALIGNMENT)))
#define pheap_obj_to_huge(a) \
    ((pheap_huge_allocation_t *)(((uint8_t *)(a)) - (sizeof(pheap_huge_allocation_t) - sizeof(pheap_allocation_t))))
#define pheap_huge_to_allocbase(huge) \
    ((void *)(((uintptr_t)huge) & PHEAP_PAGE_MASK))

#define pheap_alloc_mem(h, size) \
    (h)->config.custom_alloc \
        ? (h)->config.custom_alloc(size, (h)->config.context) \
        : pheap_system_alloc(size, pheap_is_exec((h)->flags))

#define pheap_free_mem(h, ptr, size) \
    (h)->config.custom_free \
        ? (h)->config.custom_free(ptr, size, (h)->config.context) \
        : pheap_system_free(ptr, size)

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

pheap_inline static void dlist_remove(dlist_t *entry)
{
    dlist_t *prev = entry->prev;
    dlist_t *next = entry->next;
    prev->next = next;
    next->prev = prev;
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
    uint32_t prev_off;
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
    pheap_size_t total_size;
    pheap_size_t bytes_left;
    uint8_t *unused;
}
pheap_memblock_t;

struct pheap
{
    uint64_t flags;
    size_t memblock_size;
    pheap_alloc_config_t config;
#ifdef PHEAP_USE_LOCKS
    pheap_lock_t lock;
    pheap_lock_t alloc_lock;
#endif
    dlist_t huge_list;
    dlist_t mem_list;
    dlist_t mem_buckets[PHEAP_MEMBLOCK_BUCKETS];
    dlist_t free_list[PHEAP_SIZE_BITS];
};

pheap_static_assert((PHEAP_ALLOC_OBJ_SIZE * 2) <= (PHEAP_EXTRA_SIZE_MASK + 1), object_too_big);

#ifdef PHEAP_USE_LOCKS

pheap_inline static void lock_internal_lock(pheap_internal_lock_t *lock)
{
    uint32_t spins = 0;
    for(;;)
    {
        //
        // TTAS: spin on plain load first to avoid bus traffic,
        // only attempt the atomic when the lock looks free.
        //
#ifdef _MSC_VER
        if(0 == *lock)
#else
        if(0 == __atomic_load_n(lock, __ATOMIC_RELAXED))
#endif
        {
            if(!pheap_atomic_testandset(lock, 0))
            {
                return;
            }
        }
        if(spins < 32)
        {
            pheap_pause();
        }
        else
        {
#ifdef pheap_yield
            pheap_yield();
#else
            pheap_pause();
#endif
        }
        ++spins;
    }
}

pheap_inline static void unlock_internal_lock(pheap_internal_lock_t *lock)
{
#ifdef _MSC_VER
    _InterlockedExchange(lock, 0);
#else
    __atomic_store_n(lock, 0, __ATOMIC_RELEASE);
#endif
}

pheap_inline static void init_locks(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_lock_init(&h->lock);
        pheap_lock_init(&h->alloc_lock);
    }
}

pheap_inline static void destroy_locks(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_lock_destroy(&h->lock);
        pheap_lock_destroy(&h->alloc_lock);
    }   
}

pheap_inline static void lock_pheap(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_lock_acquire(&h->lock);
    }
}

pheap_inline static void unlock_pheap(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_lock_release(&h->lock);
    }
}

pheap_inline static void lock_alloc(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_lock_acquire(&h->alloc_lock);
    }
}

pheap_inline static void unlock_alloc(pheap_t h)
{
    if(h->flags & PHEAP_FLAG_THREADSAFE)
    {
        pheap_lock_release(&h->alloc_lock);
    }
}

#else
    #define lock_internal_lock(h)     (void)h
    #define unlock_internal_lock(h)   (void)h
    #define init_locks(h)             (void)h
    #define destroy_locks(h)          (void)h
    #define lock_pheap(h)             (void)h
    #define unlock_pheap(h)           (void)h
    #define lock_alloc(h)             (void)h
    #define unlock_alloc(h)           (void)h
#endif // PHEAP_USE_LOCKS

static pheap_inline pheap_hash_t hash_pointer(const void *p, size_t memblock_size)
{
    return (pheap_hash_t)(((uintptr_t)p) / memblock_size);
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

pheap_inline static void set_previous(pheap_allocation_t *curr, void *prev)
{
    if(0 == prev)
    {
        curr->prev_off = 0;
        return;
    }
    else if(PHEAP_LIST_END_ALLOC == prev)
    {
        curr->prev_off = PHEAP_LIST_END;
        return;
    }

    pheap_assert((void *)prev < (void *)curr, "Previous is before current\n");
    curr->prev_off = (uint32_t)(((uintptr_t)curr) - ((uintptr_t)prev));
}

pheap_inline static pheap_allocation_t *get_previous(pheap_allocation_t *a)
{
    if(0 == a->prev_off)
    {
        return PHEAP_NULL;
    }
    else if(PHEAP_LIST_END == a->prev_off)
    {
        return PHEAP_LIST_END_ALLOC;
    }
    return (pheap_allocation_t *)(((uint8_t *)a) - a->prev_off);
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
    *((uint32_t *)mem->unused) = PHEAP_LIST_END;
}

pheap_inline static int memblock_can_alloc(const pheap_memblock_t *mem, int32_t alloc_size)
{
    return mem->bytes_left >= ((pheap_size_t)alloc_size + (pheap_size_t)sizeof(PHEAP_LIST_END));
}

pheap_inline static pheap_allocation_t *unchecked_allocate(pheap_t h, pheap_memblock_t *mem, int32_t size, int32_t alloc_size)
{
    pheap_allocation_t *a = (pheap_allocation_t *)mem->unused;

    take_memblock_bytes(mem, alloc_size);
    set_previous(a, mem->prev_alloc);
    set_allocated_size(a, size, alloc_size);
    a->mem_bucket = (hash_pointer(mem, h->memblock_size) % PHEAP_MEMBLOCK_BUCKETS);

    mem->prev_alloc = a;

    return a;
}

pheap_inline static pheap_allocation_t *allocate_from_existing(pheap_t h, int32_t size, int32_t alloc_size)
{
    pheap_allocation_t *a = PHEAP_NULL;
    dlist_t *next;

    lock_pheap(h);

    for(next = h->mem_list.next; next != &h->mem_list; next = next->next)
    {
        pheap_memblock_t *mem = (pheap_memblock_t *)next;

        if(memblock_can_alloc(mem, alloc_size))
        {
            a = unchecked_allocate(h, mem, size, alloc_size);
            break;
        }
    }

    unlock_pheap(h);
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
    uint32_t hash_bucket = (hash_pointer(mem, h->memblock_size) % PHEAP_MEMBLOCK_BUCKETS);

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
    pheap_size_t alloc_size;
    pheap_memblock_t *mem;
    pheap_allocation_t *a = PHEAP_NULL;
    int32_t req_size = required_alloc_size(size);

    lock_alloc(h);

    if(PHEAP_NULL != (a = allocate_from_existing(h, size, req_size)))
    {
        goto release_lock;
    }

    if(h->flags & PHEAP_FLAG_FIXED)
    {
        goto release_lock;
    }

    //
    // No more bytes, allocate another block
    //
    alloc_size = ((pheap_size_t)pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT)) + (pheap_size_t)(req_size * 2);

    if(alloc_size < req_size)
    {
        // Too large.
        goto release_lock;
    }

    if(alloc_size < (pheap_size_t)h->memblock_size)
    {
        alloc_size = h->memblock_size;
    }
    else
    {
        alloc_size = pheap_roundup2(alloc_size, h->memblock_size);
    }

    mem = pheap_alloc_mem(h, alloc_size);

    if(PHEAP_NULL != mem)
    {
        lock_pheap(h);
        memblock_init(h, mem, alloc_size);
        a = unchecked_allocate(h, mem, size, req_size);
        unlock_pheap(h);
    }

release_lock:
    unlock_alloc(h);
    return a;
}

static void release_to_memblock_end(pheap_t h, pheap_allocation_t *prev, void *a)
{
    pheap_memblock_t *mem;
    int32_t asize = get_full_alloc_size(a);
#if PHEAP_INTERNAL_DEBUG == 1
    pheap_allocation_t *next = (pheap_allocation_t *)(((uint8_t *)a) + asize);
    pheap_assert(PHEAP_LIST_END == next->prev_off, "Impossible release?");
#endif
    mem = find_memblock(h, a);
    mem->bytes_left += asize;

    if(&mem->list != h->mem_list.prev)
    {
        //
        // This is not the root-memblock that hosts the pheap structure.
        // See if it should be released back to the system.
        //
        if(mem->total_size == mem->bytes_left)
        {
            dlist_remove(&mem->list);
            dlist_remove(&mem->hash_list);
            unlock_pheap(h);

            pheap_free_mem(h, mem, mem->total_size + pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT));

            lock_pheap(h);
            return;
        }
    }

    mem->unused -= asize;
    mem->prev_alloc = prev;

    *((uint32_t *)mem->unused) = PHEAP_LIST_END;
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
    pheap_assert(next->prev_off != PHEAP_LIST_END,
        "This must be possible? Wont that break everything??");
    set_previous(next, left);
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
        set_previous(&split->allocation, a);
        split->allocation.size = split_size;
        split->allocation.extra = 0;
        split->allocation.mem_bucket = a->mem_bucket;
        //
        // [realloc_ptr] [this split] [END] => [realloc_ptr] [END]
        //
        if(PHEAP_LIST_END == next->prev_off)
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

        if(PHEAP_LIST_END == next->prev_off)
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

        set_previous(next, &split->allocation);
        release_allocation(h, split);
    }
    else
    {
        set_allocated_size(a, want_size, req_size);
        pheap_assert(((uint32_t)(a->extra & PHEAP_EXTRA_SIZE_MASK)) + ((uint32_t)(full_size - req_size)) 
                        <= PHEAP_MAX_EXTRA_SIZE, "Impossible diff? Extra has grown too large");
        a->extra += (uint8_t)(full_size - req_size);      
        next = pheap_next_allocation(a);
        if(PHEAP_LIST_END != next->prev_off)
        {
            set_previous(next, a);
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
    lock_pheap(h);
    dlist_insert_head(&h->huge_list, &a->list);
    unlock_pheap(h);
}

pheap_inline static void unlink_huge_alloc(pheap_t h, pheap_huge_allocation_t *a)
{
    lock_pheap(h);
    dlist_remove(&a->list);
    unlock_pheap(h);
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

            ptr = pheap_alloc_mem(h, rounded + PHEAP_PAGE_SIZE);

            if(PHEAP_NULL == ptr)
            {
                return PHEAP_NULL;
            }

            a = pheap_mem_to_obj(ptr + PHEAP_PAGE_SIZE);

            huge = pheap_obj_to_huge(a);
            huge->huge_size = n;

            huge->allocation.size = 0;
            huge->allocation.prev_off = 0;
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

    lock_pheap(h);
    a = allocate_from_free_bin(h, (uint32_t)n);
    unlock_pheap(h);

    if(PHEAP_NULL != a)
    {
        return pheap_obj_to_mem(a);
    }

    if(PHEAP_NULL == (a = create_allocation(h, (uint32_t)n)))
    {
        return PHEAP_NULL;
    }

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
        lock_pheap(h);
        shrink_and_split(h, curr, (int32_t)n, old_full);
        unlock_pheap(h);

        return p;
    }
    else if(n > old_size)
    {
        int32_t avail;
        int32_t req_size = required_alloc_size((int32_t)n);      
        pheap_allocation_t *next;

        lock_pheap(h);
        
        next = pheap_next_allocation(curr);

        if(next->prev_off == PHEAP_LIST_END)
        {
            //
            // Allocation is at the end of its memory block,
            // see if there are bytes left to increase the allocation...
            //
            int32_t alloc_diff = req_size - old_full;

            pheap_memblock_t *mb = find_memblock(h, curr);
            if(memblock_can_alloc(mb, alloc_diff))
            {
                take_memblock_bytes(mb, alloc_diff);
                set_allocated_size(curr, (int32_t)n, req_size);
            }
            else
            {
                unlock_pheap(h);
                return simple_realloc(h, p, n);
            }

            unlock_pheap(h);
            return p;
        }
 
        if(next->extra & PHEAP_AFLAG_IN_USE)
        {
            unlock_pheap(h);
            return simple_realloc(h, p, n);
        }

        avail = old_full + get_full_alloc_size(next);

        if(avail < req_size)
        {
            //
            // The free block after us is too small. Check if we can coalesce further:
            // either into end-of-memblock bytes, or into a second free block.
            //
            pheap_allocation_t *after_free = pheap_next_allocation(next);

            if(PHEAP_LIST_END == after_free->prev_off)
            {
                //
                // [curr] [free(small)] [END] - try extending into memblock tail
                //
                pheap_memblock_t *mb = find_memblock(h, curr);
                int32_t total_avail = avail + (int32_t)mb->bytes_left;

                if(total_avail >= req_size)
                {
                    int32_t extra_needed = req_size - avail;
                    if(memblock_can_alloc(mb, extra_needed))
                    {
                        unlink_free(next);
                        merge_free(curr, next);
                        take_memblock_bytes(mb, extra_needed);
                        curr->size += extra_needed;
                        shrink_and_split(h, curr, (int32_t)n, curr->size);
                        mb->prev_alloc = curr;
                        unlock_pheap(h);
                        return p;
                    }
                }
            }
            else if(0 == (after_free->extra & PHEAP_AFLAG_IN_USE))
            {
                //
                // [curr] [free(small)] [free] [???] - coalesce both free blocks
                //
                int32_t total_avail = avail + get_full_alloc_size(after_free);

                if(total_avail >= req_size)
                {
                    unlink_free(next);
                    unlink_free(after_free);
                    merge_free(curr, next);
                    merge_free(curr, after_free);
                    shrink_and_split(h, curr, (int32_t)n, total_avail);
                    unlock_pheap(h);
                    return p;
                }
            }

            unlock_pheap(h);
            return simple_realloc(h, p, n);
        }
        //
        // If we combine this allocation with the block after it, we have enough bytes
        // to satisfy the requested size.
        //
        merge_with_right(curr, next);
        shrink_and_split(h, curr, (int32_t)n, avail);
        unlock_pheap(h);

        return p;
    }
    //
    // Old and new size are the same, just return p
    //
    return p;
}

void pheap_free(pheap_t h, void *p)
{
    pheap_allocation_t *a;
    pheap_allocation_t *prev;
    pheap_allocation_t *next;

    if(!p)
    {
        return;
    }

    a = pheap_mem_to_obj(p);

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
        pheap_free_mem(h, ptr, huge->huge_size + PHEAP_PAGE_SIZE);

        return;
    }
    
    lock_pheap(h);

    //
    // If prev is valid and not in use, merge previous allocation with this one.
    //
    prev = get_previous(a);
    if(prev)
    {
        //
        // Are we at end?
        //
        if(PHEAP_LIST_END_ALLOC == prev)
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
            prev = get_previous(a);
        }
    }
    //
    // Always:
    // [PREV/NULL] [THIS     ] ---> [????]; resolve [????]
    //
    next = pheap_next_allocation(a);

    if(PHEAP_LIST_END == next->prev_off)
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
        set_previous(next, a);
    }
    //
    // Set this free.
    //
    release_allocation(h, a);
cleanup:
    unlock_pheap(h);
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
    h->memblock_size = PHEAP_MEMBLOCK_SIZE_HINT;
    init_locks(h);

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

    if(PHEAP_NULL == (ptr = pheap_system_alloc(size, pheap_is_exec(flags))))
    {
        // 
        return PHEAP_NULL;
    }

    return init_pheap(ptr, size, flags & ~PHEAP_FLAG_FIXED);
}

pheap_t pheap_create_custom(uint32_t flags, const pheap_alloc_config_t *config)
{
    pheap_t h;
    void *ptr;
    size_t mbs = config->memblock_size ? config->memblock_size : PHEAP_MEMBLOCK_SIZE_HINT;
    size_t size = mbs;

    if(PHEAP_NULL == (ptr = config->custom_alloc(size, (void *)config->context)))
    {
        return PHEAP_NULL;
    }

    if(PHEAP_NULL != (h = init_pheap(ptr, size, (flags & ~PHEAP_FLAG_FIXED))))
    {
        h->memblock_size = mbs;
        pheap_memcpy(&h->config, config, sizeof(h->config));
    }
    else
    {
        config->custom_free(ptr, size, (void *)config->context);
    }

    return h;
}

void pheap_destroy(pheap_t h)
{
    destroy_locks(h);

    if(h->flags & PHEAP_FLAG_FIXED)
    {
        return;
    }

    for(dlist_t *it = h->huge_list.next; it != &h->huge_list;)
    {
        dlist_t *next = it->next;
        pheap_huge_allocation_t *huge = (pheap_huge_allocation_t *)it;
        pheap_free_mem(h, pheap_huge_to_allocbase(huge), huge->huge_size + PHEAP_PAGE_SIZE);
        it = next;
    }

    for(dlist_t *it = h->mem_list.next; it != &h->mem_list;)
    {
        pheap_memblock_t *mb = (pheap_memblock_t *)it;
        pheap_size_t n = mb->total_size + pheap_roundup2(sizeof(*mb), PHEAP_ALIGNMENT);
        dlist_t *next = it->next;
        //
        // The first allocated memory block (ie the last in this list), also hosts the pheap_t structure.
        //
        if(it == h->mem_list.prev)
        {
            //
            // Destroy the heap and exit.
            //
            pheap_free_mem(h, h, n + pheap_roundup2(sizeof(*h), PHEAP_ALIGNMENT));
            break;
        }
        else
        {
            pheap_free_mem(h, mb, n);
        }

        it = next;
    }
}

#if PHEAP_USE_GLOBAL_HEAP != 0

static pheap_internal_lock_t g_init_lock = 0;
static pheap_t g_pheap = PHEAP_NULL;

pheap_inline static pheap_t pheap_global_load(void)
{
#ifdef _MSC_VER
    return (pheap_t)_InterlockedCompareExchangePointer((volatile PVOID *)&g_pheap, PHEAP_NULL, PHEAP_NULL);
#else
    return __atomic_load_n(&g_pheap, __ATOMIC_ACQUIRE);
#endif
}

pheap_inline static void pheap_global_store(pheap_t h)
{
#ifdef _MSC_VER
    _InterlockedExchangePointer((volatile PVOID *)&g_pheap, h);
#else
    __atomic_store_n(&g_pheap, h, __ATOMIC_RELEASE);
#endif
}

pheap_inline static int pheap_global_init(void)
{
    if(PHEAP_NULL == pheap_global_load())
    {
        uint32_t flags = 0;
#ifdef PHEAP_USE_LOCKS
        flags = PHEAP_FLAG_THREADSAFE;
#endif
        lock_internal_lock(&g_init_lock);
        if(PHEAP_NULL == pheap_global_load())
        {
            pheap_t h = pheap_create(flags);
            if(PHEAP_NULL == h)
            {
                unlock_internal_lock(&g_init_lock);
                pheap_trap();
                return 0;
            }
            pheap_global_store(h);
        }
        unlock_internal_lock(&g_init_lock);
    }
    return 1;
}

#if PHEAP_USE_THREAD_CACHE != 0

#define PHEAP_TCACHE_BINS       8
#define PHEAP_TCACHE_CAPACITY   32
#define PHEAP_TCACHE_MAX_SIZE   2048
#define PHEAP_TCACHE_FLUSH_COUNT 16

typedef struct pheap_tcache_bin {
    void *ptrs[PHEAP_TCACHE_CAPACITY];
    uint32_t count;
} pheap_tcache_bin_t;

typedef struct pheap_tcache {
    pheap_tcache_bin_t bins[PHEAP_TCACHE_BINS];
} pheap_tcache_t;

#ifdef _MSC_VER
    static __declspec(thread) pheap_tcache_t *tls_tcache = PHEAP_NULL;
#else
    static __thread pheap_tcache_t *tls_tcache = PHEAP_NULL;
#endif

//
// Size classes: 16, 32, 64, 128, 256, 512, 1024, 2048
// Bin index = bitscan(roundup_pow2(max(n,16))) - 4
//
pheap_inline static int tcache_size_to_bin(size_t n)
{
    uint32_t v;
    if(n < 16) n = 16;
    if(n > PHEAP_TCACHE_MAX_SIZE) return -1;
    // Round up to next power of 2
    v = (uint32_t)(n - 1);
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;
    return (int)bitscan_forward32(v) - 4;
}

pheap_inline static size_t tcache_bin_to_size(int bin)
{
    return (size_t)16 << bin;
}

static void tcache_flush_bin(pheap_tcache_bin_t *bin, pheap_t heap)
{
    uint32_t flush = PHEAP_TCACHE_FLUSH_COUNT;
    uint32_t i;
    if(flush > bin->count) flush = bin->count;

    for(i = 0; i < flush; ++i)
    {
        pheap_free(heap, bin->ptrs[bin->count - 1 - i]);
    }
    bin->count -= flush;
}

static void tcache_flush_all(pheap_tcache_t *tc, pheap_t heap)
{
    int i;
    for(i = 0; i < PHEAP_TCACHE_BINS; ++i)
    {
        pheap_tcache_bin_t *bin = &tc->bins[i];
        while(bin->count > 0)
        {
            bin->count--;
            pheap_free(heap, bin->ptrs[bin->count]);
        }
    }
}

#ifdef PHEAP_POSIX
    #include <pthread.h>
    static pthread_key_t g_tcache_key;
    static pheap_internal_lock_t g_tcache_key_lock = 0;
    static int g_tcache_key_created = 0;

    static void tcache_thread_destructor(void *ptr)
    {
        pheap_tcache_t *tc = (pheap_tcache_t *)ptr;
        if(tc)
        {
            pheap_t heap = pheap_global_load();
            if(heap)
            {
                tcache_flush_all(tc, heap);
            }
            pheap_system_free(tc, sizeof(pheap_tcache_t));
        }
    }

    static void tcache_ensure_key(void)
    {
        if(!g_tcache_key_created)
        {
            lock_internal_lock(&g_tcache_key_lock);
            if(!g_tcache_key_created)
            {
                pthread_key_create(&g_tcache_key, tcache_thread_destructor);
                g_tcache_key_created = 1;
            }
            unlock_internal_lock(&g_tcache_key_lock);
        }
    }
#elif defined(PHEAP_WIN)
    static DWORD g_tcache_fls = FLS_OUT_OF_INDEXES;
    static pheap_internal_lock_t g_tcache_fls_lock = 0;

    static VOID NTAPI tcache_fls_callback(PVOID ptr)
    {
        pheap_tcache_t *tc = (pheap_tcache_t *)ptr;
        if(tc)
        {
            pheap_t heap = pheap_global_load();
            if(heap)
            {
                tcache_flush_all(tc, heap);
            }
            VirtualFree(tc, 0, MEM_RELEASE);
        }
    }

    static void tcache_ensure_key(void)
    {
        if(g_tcache_fls == FLS_OUT_OF_INDEXES)
        {
            lock_internal_lock(&g_tcache_fls_lock);
            if(g_tcache_fls == FLS_OUT_OF_INDEXES)
            {
                g_tcache_fls = FlsAlloc(tcache_fls_callback);
            }
            unlock_internal_lock(&g_tcache_fls_lock);
        }
    }
#endif

static pheap_tcache_t *tcache_get_or_create(void)
{
    pheap_tcache_t *tc = tls_tcache;
    if(tc) return tc;

    tcache_ensure_key();

#ifdef PHEAP_POSIX
    tc = (pheap_tcache_t *)pheap_system_alloc(sizeof(pheap_tcache_t), 0);
    if(PHEAP_NULL == tc) return PHEAP_NULL;
    pheap_memset(tc, 0, sizeof(*tc));
    tls_tcache = tc;
    pthread_setspecific(g_tcache_key, tc);
#elif defined(PHEAP_WIN)
    tc = (pheap_tcache_t *)VirtualAlloc(PHEAP_NULL, sizeof(pheap_tcache_t),
                                         MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    if(PHEAP_NULL == tc) return PHEAP_NULL;
    pheap_memset(tc, 0, sizeof(*tc));
    tls_tcache = tc;
    FlsSetValue(g_tcache_fls, tc);
#endif

    return tc;
}

pheap_inline static void *tcache_alloc(size_t n)
{
    int bin_idx;
    pheap_tcache_t *tc;
    pheap_tcache_bin_t *bin;

    bin_idx = tcache_size_to_bin(n);
    if(bin_idx < 0) return PHEAP_NULL;

    tc = tcache_get_or_create();
    if(PHEAP_NULL == tc) return PHEAP_NULL;

    bin = &tc->bins[bin_idx];
    if(bin->count > 0)
    {
        bin->count--;
        return bin->ptrs[bin->count];
    }

    return PHEAP_NULL;
}

pheap_inline static int tcache_free(void *p, size_t alloc_size)
{
    int bin_idx;
    pheap_tcache_t *tc;
    pheap_tcache_bin_t *bin;

    if(alloc_size > PHEAP_TCACHE_MAX_SIZE) return 0;

    bin_idx = tcache_size_to_bin(alloc_size);
    if(bin_idx < 0) return 0;

    tc = tcache_get_or_create();
    if(PHEAP_NULL == tc) return 0;

    bin = &tc->bins[bin_idx];
    if(bin->count >= PHEAP_TCACHE_CAPACITY)
    {
        tcache_flush_bin(bin, pheap_global_load());
    }

    bin->ptrs[bin->count] = p;
    bin->count++;
    return 1;
}

#endif // PHEAP_USE_THREAD_CACHE

void *pheap_g_alloc(size_t n)
{
    if(!pheap_global_init())
    {
        return PHEAP_NULL;
    }
#if PHEAP_USE_THREAD_CACHE != 0
    {
        int bin_idx = tcache_size_to_bin(n);
        if(bin_idx >= 0)
        {
            void *p = tcache_alloc(n);
            if(p) return p;
            return pheap_alloc(pheap_global_load(), tcache_bin_to_size(bin_idx));
        }
    }
#endif
    return pheap_alloc(pheap_global_load(), n);
}

void *pheap_g_zalloc(size_t n)
{
    if(!pheap_global_init())
    {
        return PHEAP_NULL;
    }
#if PHEAP_USE_THREAD_CACHE != 0
    {
        int bin_idx = tcache_size_to_bin(n);
        if(bin_idx >= 0)
        {
            void *p = tcache_alloc(n);
            if(p)
            {
                pheap_memset(p, 0, n);
                return p;
            }
            return pheap_zalloc(pheap_global_load(), tcache_bin_to_size(bin_idx));
        }
    }
#endif
    return pheap_zalloc(pheap_global_load(), n);
}

void *pheap_g_realloc(void *p, size_t n)
{
    if(!pheap_global_init())
    {
        return PHEAP_NULL;
    }
#if PHEAP_USE_THREAD_CACHE != 0
    if(p)
    {
        size_t old_size = pheap_msize(p);
        void *np = pheap_g_alloc(n);
        if(PHEAP_NULL == np) return PHEAP_NULL;
        pheap_memcpy(np, p, (n < old_size) ? n : old_size);
        pheap_g_free(p);
        return np;
    }
    return pheap_g_alloc(n);
#else
    return pheap_realloc(pheap_global_load(), p, n);
#endif
}

void pheap_g_free(void *p)
{
    if(!p) return;
#if PHEAP_USE_THREAD_CACHE != 0
    {
        pheap_allocation_t *a = pheap_mem_to_obj(p);
        if(!(a->extra & PHEAP_AFLAG_IS_HUGE))
        {
            size_t sz = (size_t)a->size;
            if(tcache_free(p, sz)) return;
        }
    }
#endif
    pheap_free(pheap_global_load(), p);
}

#endif

#ifdef PHEAP_TEST

#define dlist_is_empty(head) (head == head->next)

int pheap_test_is_pristine(pheap_t h)
{
    dlist_t *huge = &h->huge_list;

    if(!dlist_is_empty(huge))
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
        dlist_t *fl = h->free_list + i;
        if(!dlist_is_empty(fl))
        {
            return 0;
        }
    }

    return 1;
}

#endif // PHEAP_TEST

#ifdef _MSC_VER
#pragma warning(pop)
#endif


