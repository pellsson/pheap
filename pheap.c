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

pheap_static_assert(PHEAP_PAGE_SIZE < PHEAP_MEMBLOCK_SIZE_HINT, hint_too_small);

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
		_BitScanForward(&tmp, v);
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
	
	#define pheap_trap()	// Trap the processor
	#define pheap_inline	// Inline directive

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
#endif

#if PHEAP_NATIVE_ALLOC == 1
	#if defined(PHEAP_WIN)
	static void *pheap_native_alloc(size_t n)
	{
		return VirtualAlloc(PHEAP_NULL, n, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
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
	//
	// Assume everything but Windows has mmap()
	//
	static void *pheap_native_alloc(size_t n)
	{
		return mmap(0, n, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
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
	void *pheap_native_alloc(size_t n);
	void pheap_native_destroy(void *p, size_t n);
#endif // PHEAP_NATIVE_ALLOC

#if PHEAP_LOCK_PRIMITIVE != PHEAP_NO_LOCK
	#define PHEAP_USE_LOCKS
#endif

#if PHEAP_LOCK_PRIMITIVE == PHEAP_PTHREAD_LOCK
	#include <pthread.h>
	typedef pthread_mutex_t pheap_lock_t;
	#define pheap_init_lock(h) if(h->flags & PHEAP_FLAG_THREADSAFE) { pthread_mutex_init(&h->lock, NULL); }
	#define pheap_uninit_lock(h) if(h->flags & PHEAP_FLAG_THREADSAFE) { pthread_mutex_destroy(&h->lock); }
	#define pheap_lock(h) if(h->flags & PHEAP_FLAG_THREADSAFE) { pthread_mutex_lock(&h->lock); }
	#define pheap_unlock(h) if(h->flags & PHEAP_FLAG_THREADSAFE) { pthread_mutex_unlock(&h->lock); }
#elif PHEAP_LOCK_PRIMITIVE == PHEAP_WIN32_LOCK
	#ifndef PHEAP_WIN
		#error You can only use win32 locking on Windows...
	#endif
	typedef CRITICAL_SECTION pheap_lock_t;
	#define pheap_init_lock(h) if(h->flags & PHEAP_FLAG_THREADSAFE) { InitializeCriticalSection(&h->lock); }
	#define pheap_uninit_lock(h) if(h->flags & PHEAP_FLAG_THREADSAFE) { DeleteCriticalSection(&h->lock); }
	#define	pheap_lock(h) if(h->flags & PHEAP_FLAG_THREADSAFE) { EnterCriticalSection(&h->lock); }
	#define pheap_unlock(h) if(h->flags & PHEAP_FLAG_THREADSAFE) { LeaveCriticalSection(&h->lock); }
#elif PHEAP_LOCK_PRIMITIVE == PHEAP_INTERNAL_LOCK
	typedef pheap_internal_lock_t pheap_lock_t;
#else
	#define pheap_init_lock(h)
	#define pheap_uninit_lock(h)
	#define	pheap_lock(h)
	#define pheap_unlock(h)
#endif

#define PHEAP_FLAG_IN_USE	0x80000000
#define PHEAP_FLAG_IS_HUGE	0x40000000
#define PHEAP_SIZE_MASK		0x0FFFFFFF
#define PHEAP_SIZE_BITS		(32-4)

#define PHEAP_MAX_FREEBIN_SCANS	8

#define PHEAP_LIST_END ((void *)((uintptr_t)0xFFFFFFFFFFFFFFFFULL))

typedef uint8_t pheap_hash_t;

#define PHEAP_MEMBLOCK_BUCKETS	(1<<sizeof(pheap_hash_t))
#define PHEAP_HUGE_SIZE_MASK	((((size_t)0) - ((size_t)1)) & ~((size_t)PHEAP_SIZE_MASK))
#define	PHEAP_ALLOC_OBJ_SIZE	((int32_t)pheap_roundup2(sizeof(pheap_allocation_free_t), PHEAP_ALIGNMENT))
#define PHEAP_FREE_DIFF			((int32_t)(PHEAP_ALLOC_OBJ_SIZE - pheap_roundup2(sizeof(pheap_allocation_t), PHEAP_ALIGNMENT)))
#define PHEAP_PAGE_MASK			(~((size_t)(PHEAP_PAGE_SIZE - 1)))

#define pheap_roundup2(val, by)	(((val) + ((by) - 1)) & (~((by) - 1)))

#define pheap_next_allocation(a)		(void *)(((uint8_t *)a) + get_full_alloc_size(a));
// TODO : I think this is wrong...?
#define pheap_search_dir_forward(n, s)	((n > ((s) - (((s) - ((s) >> 1)) / 2))) ? 1 : 0)

#define pheap_obj_to_mem(a) \
	((void *)(((uint8_t *)(a)) + pheap_roundup2(sizeof(pheap_allocation_t), PHEAP_ALIGNMENT)))
#define pheap_mem_to_obj(m) \
	((pheap_allocation_t *)(((uint8_t *)(m)) - pheap_roundup2(sizeof(pheap_allocation_t), PHEAP_ALIGNMENT)))
#define pheap_obj_to_huge(a) \
	((pheap_huge_allocation_t *)(((uint8_t *)(a)) - (sizeof(pheap_huge_allocation_t) - sizeof(pheap_allocation_t))))
#define pheap_huge_to_allocbase(huge) \
	((void *)(((uintptr_t)huge) & PHEAP_PAGE_MASK))

#pragma pack(push, 1)

typedef struct pheap_allocation
{
	struct pheap_allocation *prev;
	// When allocated, requested allocation size
	// When free, size of entire allocation.
	int32_t size;
	pheap_hash_t mem_bucket;
	// When allocated, add this with size to get allocation size
	// When free, always zero
	int8_t extra_size;
}
pheap_allocation_t;

typedef struct pheap_huge_allocation
{
	struct pheap_huge_allocation *next;
	struct pheap_huge_allocation *prev;
	size_t huge_size;
	pheap_allocation_t allocation;
}
pheap_huge_allocation_t;

typedef struct pheap_huge_list
{
	pheap_huge_allocation_t *head;
	pheap_huge_allocation_t *tail;
}
pheap_huge_list_t;

pheap_static_assert(sizeof(pheap_huge_allocation_t) <= PHEAP_PAGE_SIZE, page_size_too_small);

typedef struct pheap_allocation_free
{
	pheap_allocation_t allocation;

	struct pheap_allocation_free *prev;
	struct pheap_allocation_free *next;
}
pheap_allocation_free_t;

typedef struct pheap_free_list
{
	struct pheap_allocation_free *tail;
	struct pheap_allocation_free *head;
}
pheap_free_list_t;

#pragma pack(pop)

typedef struct pheap_memblock
{
	struct pheap_memblock *next_slist;
	struct pheap_memblock *next_hash;
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
	pheap_huge_list_t huge_list;
	pheap_memblock_t *mem_list;
	pheap_memblock_t *mem_buckets[PHEAP_MEMBLOCK_BUCKETS];
	pheap_free_list_t free_list[PHEAP_SIZE_BITS];
};

pheap_inline static void pheap_internal_lock_lock(pheap_internal_lock_t *lock)
{
	while(pheap_atomic_testandset(lock, 1))
	{
		pheap_pause();
	}
}

pheap_inline static void pheap_internal_lock_unlock(pheap_internal_lock_t *lock)
{
	*lock = 0;
}

#if PHEAP_LOCK_PRIMITIVE == PHEAP_INTERNAL_LOCK

pheap_inline static void pheap_init_lock(pheap_t h)
{
	if(h->flags & PHEAP_FLAG_THREADSAFE)
	{
		pheap_internal_lock_unlock(&h->lock);
	}
}

#define pheap_uninit_lock(h) // nothing to do here

pheap_inline static void pheap_lock(pheap_t h)
{
	if(h->flags & PHEAP_FLAG_THREADSAFE)
	{
		pheap_internal_lock_lock(&h->lock);
	}
}

pheap_inline static void pheap_unlock(pheap_t h)
{
	if(h->flags & PHEAP_FLAG_THREADSAFE)
	{
		pheap_internal_lock_unlock(&h->lock);
	}
}

#endif // PHEAP_LOCK_PRIMITIVE == PHEAP_INTERNAL_LOCK

//
// Word-size specific stuff
//
#if PHEAP_WORDSIZE == PHEAP_64BIT

static pheap_inline pheap_hash_t hash_pointer(const void *p)
{
	uint64_t v = (uint64_t)((uintptr_t)p);
	// TODO - this is very x64 0x1000-page-size-specific. But its probably ok...
	return (uint32_t)(((v >> 16) & 0xFFFFFF) | ((v >> (24 + 16)) * 13));
}

#elif PHEAP_WORDSIZE == PHEAP_32BIT

static pheap_inline pheap_hash_t hash_pointer(const void *p)
{
	uint32_t v = (uint32_t)((uintptr_t)p);
	return ((v >> 0x10) * 13);
}

#else

#error Unable to determine word-width, please set PHEAP_WORDSIZE manually.

#endif

#if PHEAP_INTERNAL_DEBUG == 0
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
	#define pheap_impossible(s)	pheap_trap()
	#define pheap_assert(x, s)
#endif


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

pheap_inline static void unlink_free_list(pheap_free_list_t *list, pheap_allocation_free_t *f)
{
	if(PHEAP_NULL == list->head)
	{
		pheap_impossible("Attempting to unlink an empty list - Something got out of sync...\n");
	}

	if(!f->prev)
	{
		list->head = f->next;
	}
	else
	{
		f->prev->next = f->next;
	}

	if(!f->next)
	{
		list->tail = f->prev;
	}
	else
	{
		f->next->prev = f->prev;
	}
}

pheap_inline static void unlink_free(pheap_t h, void *ptr)
{
	pheap_allocation_free_t *f = (pheap_allocation_free_t *)ptr;
	unlink_free_list(h->free_list + size_to_index(f->allocation.size & PHEAP_SIZE_MASK, PHEAP_NULL), f);
}

pheap_inline static void free_insert_after(pheap_free_list_t *dlist, pheap_allocation_free_t *after, pheap_allocation_free_t *ins)
{
	if(!after)
	{
		ins->next = ins->prev = PHEAP_NULL;
		dlist->tail = dlist->head = ins;
		return;
	}

	ins->next	= after->next;
	ins->prev	= after;
	after->next = ins;
	
	if(ins->next)
	{
		ins->next->prev = ins;
	}
	else
	{
		dlist->tail = ins;
	}
}

pheap_inline static void free_insert_before(pheap_free_list_t *dlist, pheap_allocation_free_t *before, pheap_allocation_free_t *ins)
{
	if(!before)
	{
		ins->next = ins->prev = PHEAP_NULL;
		dlist->tail = dlist->head = ins;
		return;
	}

	ins->prev	 = before->prev;
	ins->next	 = before;
	before->prev = ins;

	if(ins->prev)
	{
		ins->prev->next = ins;
	}
	else
	{
		dlist->head = ins;
	}
}

pheap_inline static void make_free(void *a)
{
	pheap_allocation_free_t *f = a;

	if(f->allocation.size & PHEAP_FLAG_IN_USE)
	{
		f->allocation.size &= PHEAP_SIZE_MASK;
		f->allocation.size += f->allocation.extra_size;
		f->allocation.extra_size = 0;
	}
}

pheap_inline static int32_t get_full_alloc_size(const pheap_allocation_t *a)
{
	return ((a->size & PHEAP_SIZE_MASK) + a->extra_size);
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
	pheap_free_list_t *list;

	make_free(a);
	
	f->next = f->prev = PHEAP_NULL;
	list = (h->free_list + size_to_index(f->allocation.size, &bucket_upper_bound));

	if(pheap_search_dir_forward(f->allocation.size, bucket_upper_bound))
	{
		//
		// Push to head
		//
		free_insert_before(list, list->head, f);
	}
	else
	{
		//
		// Push to tail
		//
		free_insert_after(list, list->tail, f);
	}
}

pheap_inline static pheap_allocation_t *unchecked_allocate(pheap_memblock_t *mem, int32_t size, int32_t alloc_size)
{
	pheap_allocation_t *a;

	mem->bytes_left -= alloc_size;
	a = (pheap_allocation_t *)mem->unused;
	mem->unused += alloc_size;

	a->prev = mem->prev_alloc;
	a->size = (size | PHEAP_FLAG_IN_USE);
	a->extra_size = (alloc_size - size);

	a->mem_bucket = (hash_pointer(mem) % PHEAP_MEMBLOCK_BUCKETS);

	mem->prev_alloc = a;
	*((void **)mem->unused) = PHEAP_LIST_END;

	return a;
}

pheap_inline static pheap_allocation_t *allocate_from_existing(pheap_t h, int32_t size, int32_t alloc_size)
{
	pheap_allocation_t *a = PHEAP_NULL;
	pheap_memblock_t *mem;

	ssize_t size_with_end = ((ssize_t)alloc_size + (ssize_t)sizeof(PHEAP_LIST_END));

	for(mem = h->mem_list; mem; mem = mem->next_slist)
	{
		if(mem->bytes_left >= size_with_end)
		{
			int32_t spare_after = (int32_t)(mem->bytes_left - size_with_end);
			//
			// If there are not enough bytes left in the block to create more allocations,
			// just add the spare bytes to this allocation.
			//
			if(spare_after < PHEAP_ALLOC_OBJ_SIZE)
			{
				alloc_size += spare_after;
			}

			a = unchecked_allocate(mem, size, alloc_size);
			break;
		}
	}
	
	return a;	
}

pheap_inline static pheap_memblock_t *find_memblock(pheap_t h, const pheap_allocation_t *a)
{
	pheap_memblock_t *mem = h->mem_buckets[a->mem_bucket];
	const uint8_t *ptr = (const uint8_t *)a; 

	for(; mem; mem = mem->next_hash)
	{
		const uint8_t *start = ((const uint8_t *)mem) + pheap_roundup2(sizeof(*mem), PHEAP_ALIGNMENT);
		const uint8_t *end = start + mem->total_size;

		if(ptr >= start && ptr < end)
		{
			return mem;
		}
	}

	pheap_impossible("Unable to locate memblock from which data was freed (everything broken)\n");
	return PHEAP_NULL;
}

pheap_inline static void memblock_init(pheap_t h, pheap_memblock_t *mem, size_t alloced)
{
	uint32_t hash_bucket = (hash_pointer(mem) % PHEAP_MEMBLOCK_BUCKETS);

	mem->next_slist = h->mem_list;
	h->mem_list = mem;
	mem->next_hash = h->mem_buckets[hash_bucket];
	h->mem_buckets[hash_bucket] = mem;

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

	if(PHEAP_NULL != (mem = pheap_native_alloc(alloc_size)))
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
	pheap_allocation_t *next = (pheap_allocation_t *)(((uint8_t *)a) + asize);

	pheap_assert(PHEAP_LIST_END == next->prev, "Impossible release?");

	mem = find_memblock(h, a);
	mem->bytes_left += asize;
	mem->unused -= asize;
	mem->prev_alloc = prev;

	*((void **)mem->unused) = PHEAP_LIST_END;
}

static void merge_with_right(pheap_t h, void *left, void *right)
{
	pheap_allocation_t *next;

	pheap_assert(!(((pheap_allocation_t *)right)->size & PHEAP_FLAG_IN_USE), "Cant merge right with used block");

	unlink_free(h, right);
	merge_free(left, right);

	next = pheap_next_allocation(left);
	pheap_assert(next->size & PHEAP_FLAG_IN_USE, 
		"Object following end-merge is not in use, this should be impossible.\n");
	pheap_assert(next->prev != PHEAP_LIST_END,
		"This must be possible? Wont that break everything??");
	next->prev = left;
}

static pheap_allocation_t *claim_free_bin(pheap_t h, pheap_free_list_t *list, pheap_allocation_free_t *f, int32_t size)
{
	int32_t req_size = required_alloc_size(size);
	int32_t trailing_bytes = (f->allocation.size - req_size);

	unlink_free_list(list, f);

	if(trailing_bytes >= PHEAP_ALLOC_OBJ_SIZE)
	{
		pheap_allocation_free_t *split;
		pheap_allocation_t *next;
		//
		// We are allocating from a larger free bucket.
		// Need to split the allocation and add the later part back to the free list.
		//
		next = pheap_next_allocation(&f->allocation);

		f->allocation.size = PHEAP_FLAG_IN_USE | size;
		f->allocation.extra_size = req_size - size;

		split = pheap_next_allocation(&f->allocation);

		split->allocation.prev = &f->allocation;
		split->allocation.size = trailing_bytes;
		split->allocation.extra_size = 0;
		split->allocation.mem_bucket = f->allocation.mem_bucket;

		next = pheap_next_allocation(&split->allocation);

		if(PHEAP_LIST_END == next->prev)
		{
			release_to_memblock_end(h, &f->allocation, split);
		}
		else
		{
			pheap_assert((next->size & PHEAP_FLAG_IN_USE), "What???");

			next->prev = &split->allocation;
			release_allocation(h, split);
		}
	}
	else
	{
		f->allocation.extra_size = (f->allocation.size - size);
		f->allocation.size = PHEAP_FLAG_IN_USE | size;
	}
	return (pheap_allocation_t *)f;
}

static pheap_allocation_t *allocate_from_free_bin(pheap_t h, int32_t size)
{
	pheap_allocation_free_t *ret = PHEAP_NULL;

	int32_t req_size = required_alloc_size(size);

	uint32_t i = 0;
	int32_t upper;

	uint32_t index = size_to_index(req_size, &upper);
	pheap_free_list_t *list = (h->free_list + index);

	int search_fwd = pheap_search_dir_forward(req_size, upper);

	ret = search_fwd ? list->head : list->tail;

	while(ret)
	{
		if(ret->allocation.size >= req_size)
		{
			return claim_free_bin(h, list, ret, size);
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
			ret = ret->next;
		}
		else
		{
			ret = ret->prev;
		}
	}

	for(i = (index + 1); i < PHEAP_SIZE_BITS; ++i)
	{
		list = (h->free_list + i);
		if(list->tail)
		{
			return claim_free_bin(h, list, list->tail, size);
		}
	}

	return PHEAP_NULL;
}

pheap_inline static void unsafe_link_huge_alloc(pheap_t h, pheap_huge_allocation_t *a)
{
	pheap_huge_allocation_t *after;

	a->next = PHEAP_NULL;
	a->prev = PHEAP_NULL;

	after = h->huge_list.tail;

	if(PHEAP_NULL == after)
	{
		a->next = a->prev = PHEAP_NULL;
		h->huge_list.head = h->huge_list.tail = a;
	}
	else
	{
		a->next	= after->next;
		a->prev	= after;
		after->next = a;
	
		if(a->next)
		{
			a->next->prev = a;
		}
		else
		{
			h->huge_list.tail = a;
		}
	}
}

pheap_inline static void unsafe_unlink_huge_alloc(pheap_t h, pheap_huge_allocation_t *a)
{
	if(!a->prev)
	{
		h->huge_list.head = a->next;
	}
	else
	{
		a->prev->next = a->next;
	}

	if(!a->next)
	{
		h->huge_list.tail = a->prev;
	}
	else
	{
		a->next->prev = a->prev;
	}
}

pheap_inline static void link_huge_alloc(pheap_t h, pheap_huge_allocation_t *a)
{
	pheap_lock(h);
	unsafe_link_huge_alloc(h, a);
	pheap_unlock(h);
}

pheap_inline static void unlink_huge_alloc(pheap_t h, pheap_huge_allocation_t *a)
{
	pheap_lock(h);
	unsafe_unlink_huge_alloc(h, a);
	pheap_unlock(h);
}

void *pheap_alloc(pheap_t h, size_t n)
{
	pheap_allocation_t *a;

	if((n & PHEAP_HUGE_SIZE_MASK)
	|| ((n + sizeof(pheap_allocation_free_t)) & PHEAP_HUGE_SIZE_MASK))
	{
		uint8_t *ptr;
		pheap_huge_allocation_t *huge;
		size_t rounded = pheap_roundup2(n, PHEAP_PAGE_SIZE);

		if(rounded < n)
		{
			return PHEAP_NULL;
		}
		if(PHEAP_NULL == (ptr = pheap_native_alloc(rounded + PHEAP_PAGE_SIZE)))
		{
			return PHEAP_NULL;
		}

		a = pheap_mem_to_obj(ptr + PHEAP_PAGE_SIZE);

		huge = pheap_obj_to_huge(a);
		huge->huge_size = n;

		huge->allocation.size = PHEAP_FLAG_IN_USE | PHEAP_FLAG_IS_HUGE;
		huge->allocation.prev = PHEAP_NULL;
		huge->allocation.extra_size = 0;
		huge->allocation.mem_bucket = 0;
		
		link_huge_alloc(h, huge);
		return (ptr + PHEAP_PAGE_SIZE);
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

void *pheap_realloc(pheap_t h, void *p, size_t n)
{
	void *ptr;
	size_t old_size;

	if(PHEAP_NULL == p)
	{
		return pheap_alloc(h, n);
	}

	old_size = pheap_msize(p);

	if(PHEAP_NULL == (ptr = pheap_alloc(h, n)))
	{
		return PHEAP_NULL;
	}

	pheap_memcpy(ptr, p, (n < old_size) ? n : old_size);
	return ptr;
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
	if(0 == (PHEAP_FLAG_IN_USE & a->size))
	{
		pheap_impossible("Object being free is not in use (or not a pheap allocation)\n");
	}
	else if(PHEAP_FLAG_IS_HUGE & a->size)
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
		// Either:
		// [FREE] [THIS] [????]
		// or:
		// [USED] [THIS] [????]
		//
		if(0 == (prev->size & PHEAP_FLAG_IN_USE))
		{
			//
			// [FREE] [THIS] ---> [THIS    ]
			// The block before this block is also free. Merge the two.
			//
			unlink_free(h, prev);
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
	else if(0 == (PHEAP_FLAG_IN_USE & next->size))
	{
		merge_with_right(h, a, next);
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
	if(PHEAP_FLAG_IS_HUGE & a->size)
	{
		return pheap_obj_to_huge(a)->huge_size;
	}
	return a->size & PHEAP_SIZE_MASK;
}

pheap_t pheap_create(uint32_t flags)
{
	pheap_t h;
	uint8_t *p;
	pheap_memblock_t *mb;
	size_t size = PHEAP_MEMBLOCK_SIZE_HINT;

	if(0 == (h = pheap_native_alloc(size)))
	{
		// 
		return PHEAP_NULL;
	}

	pheap_memset(h, 0, sizeof(*p));

	h->flags = flags;
	pheap_init_lock(h);

	p = (uint8_t *)h;
	mb = (pheap_memblock_t *)(p + pheap_roundup2(sizeof(*h), PHEAP_ALIGNMENT));

	memblock_init(h, mb, size - pheap_roundup2(sizeof(*h), PHEAP_ALIGNMENT));

	return h;
}

void pheap_destory(pheap_t h)
{
	pheap_memblock_t *mb = h->mem_list;
	pheap_huge_allocation_t *huge;

	pheap_uninit_lock(h);

	huge = h->huge_list.head;
	while(huge)
	{
		pheap_huge_allocation_t *next = huge->next;
		pheap_native_destroy(pheap_huge_to_allocbase(huge), huge->huge_size + PHEAP_PAGE_SIZE);
		huge = next;
	}

	while(mb)
	{
		ssize_t n = mb->total_size + pheap_roundup2(sizeof(*mb), PHEAP_ALIGNMENT);
		pheap_memblock_t *next = mb->next_slist;
		//
		// The first allocated memory block (ie the last in this list), also hosts the pheap_t structure.
		//
		if(PHEAP_NULL == next)
		{
			pheap_native_destroy(h, n + pheap_roundup2(sizeof(*h), PHEAP_ALIGNMENT));
		}
		else
		{
			pheap_native_destroy(mb, n);
		}

		mb = next;
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
		pheap_internal_lock_lock(&g_init_lock);
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
		pheap_internal_lock_unlock(&g_init_lock);
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
	pheap_memblock_t *mb;
	if(PHEAP_NULL != h->huge_list.head || PHEAP_NULL != h->huge_list.tail)
	{
		return 0;
	}
	for(mb = h->mem_list; mb; mb = mb->next_slist)
	{
		if(mb->bytes_left != mb->total_size)
		{
			return 0;
		}
	}
	for(int i = 0; i < PHEAP_SIZE_BITS; ++i)
	{
		pheap_free_list_t *list = (h->free_list + i);
		if((list->tail != PHEAP_NULL) || (list->head != PHEAP_NULL))
		{
			return 0;
		}
	}

	return 1;
}

#endif // PHEAP_TEST

