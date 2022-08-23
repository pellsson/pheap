#ifndef __PHEAP_H_DEF__
#define __PHEAP_H_DEF__

//
// ### Start of config ###
//
// Set the configs to 1 or 0 to override their default values
//

// PHEAP_ALIGNMENT
// Sets memory alignment.
#ifndef PHEAP_ALIGNMENT
	#define PHEAP_ALIGNMENT	0x10 // **MUST** be power of two. Set to 1 if you want no alignment
#endif

// PHEAP_USE_C_STDLIB
// TODO XXX write comment.
#ifndef PHEAP_USE_C_STD
	#define PHEAP_USE_C_STD 1
#endif

// PHEAP_NATIVE_ALLOC
// Use OS-native (VirtualAlloc or mmap) allocation functions.
// If not defined, your code must implement the following functions:
//    void *pheap_native_alloc(size_t n);
//    void pheap_native_destroy(void *p, size_t n);
#ifndef PHEAP_NATIVE_ALLOC
	#define PHEAP_NATIVE_ALLOC 1
#endif

// PHEAP_LOCK_PRIMITIVE
// Can be one of the following:
#define PHEAP_NO_LOCK 0			// Completely disable all locks. Trying to create thread-safe heap will fail.
#define PHEAP_WIN32_LOCK 1		// Use native win32-lock (CRITICAL_SECTION)
#define PHEAP_PTHREAD_LOCK 2	// Use pthread_mutex_t
#define PHEAP_INTERNAL_LOCK 3	// Use cross-platform internal spinlock
#define PHEAP_CUSTOM_LOCK 4		// Use your own lock implementation. See pheap.c for information on how.

#ifndef PHEAP_LOCK_PRIMITIVE
	#ifdef _WIN32
		#define PHEAP_LOCK_PRIMITIVE PHEAP_WIN32_LOCK
	#else
		#define PHEAP_LOCK_PRIMITIVE PHEAP_PTHREAD_LOCK
	#endif
#endif

// PHEAP_INTERNAL_DEBUG
// If the tests fail or crash, define this to help you with debugging.
#ifndef PHEAP_INTERNAL_DEBUG
	#define PHEAP_INTERNAL_DEBUG 0
#endif

// PHEAP_PAGE_SIZE
// Size of the smallest native page (if unsure just leave it).
#ifndef PHEAP_PAGE_SIZE
	#define PHEAP_PAGE_SIZE 0x1000 // *MUST* be a power of 2
#endif

// PHEAP_USE_GLOBAL_HEAP
// Will create a global heap that can be accessed anywhere.
// If PHEAP_LOCK_PRIMITIVE is not PHEAP_NO_LOCK, the global heap is thread-safe
#ifndef PHEAP_USE_GLOBAL_HEAP
	#define PHEAP_USE_GLOBAL_HEAP 0
#endif

// PHEAP_GLOBAL_REPLACE_MALLOC
// If this is defined, the global PHEAP will take the place of malloc & friends.
#ifndef PHEAP_GLOBAL_REPLACE_MALLOC
	#define PHEAP_GLOBAL_REPLACE_MALLOC 0
#endif

//
// ### End of config ###
//

#if PHEAP_GLOBAL_REPLACE_MALLOC != 0 && PHEAP_USE_GLOBAL_HEAP == 0
	#error You must set PHEAP_USE_GLOBAL_HEAP to 1 if you want to use PHEAP_GLOBAL_REPLACE_MALLOC.
#endif

#if PHEAP_GLOBAL_REPLACE_MALLOC != 0
	#define malloc pheap_g_alloc
	#define calloc(a, b) pheap_g_zalloc(a * b);
	#define realloc pheap_g_realloc
	#define free pheap_g_free
	#define msize pheap_msize
#endif

#if PHEAP_USE_C_STD == 1
	#include <stddef.h>
	#include <stdint.h>
	#include <string.h>

	#define pheap_memset	memset
	#define pheap_memcpy	memcpy
	#define PHEAP_NULL		NULL
#else
	#error If you dont have a C-runtime, you must manually implement the PHEAP requirements.
	//
	// ### PHEAP requirements ###
	//
	// PHEAP_NULL - Invalid pointer address, usually 0
	// pheap_memset - void *pheap_memset(void * ptr, int value, size_t num) (return value not used).
	// pheap_memcpy - void *pheap_memcpy(void * dest, const void *src, size_t n) (return value not used).
	// size_t - Integer big enough to hold biggest possible allocation.
	// And the stdint.h types:
	//    uint8_t, uint16_t, uint32_t, uint64_t, uintptr_t
	//    int8_t, int16_t, int32_t, int64_t, intptr_t
	//
	// Optionally, if you use PHEAP_INTERNAL_LOCK, you can define
	// pheap_yield (commonly a sleep(0)) which will greatly increase
	// performance (and reduce cpu-usage) on the internal locks.
	//
#endif

//
// TODO Remove this constant in version 2.0 when add reserve+commit.
//
#ifdef PHEAP_TEST
	#define PHEAP_MEMBLOCK_SIZE_HINT 0x10000
#else
	#define PHEAP_MEMBLOCK_SIZE_HINT 32 * 0x100000
#endif

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct pheap * pheap_t;

#if PHEAP_LOCK_PRIMITIVE != PHEAP_NO_LOCK
	#define PHEAP_FLAG_THREADSAFE 1
#endif

pheap_t pheap_create(uint32_t flags);
void pheap_destory(pheap_t h);

void *pheap_alloc(pheap_t h, size_t n);
void *pheap_zalloc(pheap_t h, size_t n);
void *pheap_realloc(pheap_t h, void *p, size_t n);
void pheap_free(pheap_t h, void *p);

void *pheap_g_alloc(size_t n);
void *pheap_g_zalloc(size_t n);
void *pheap_g_realloc(void *p, size_t n);
void pheap_g_free(void *p);

size_t pheap_msize(const void *p);

#ifdef PHEAP_TEST
int pheap_test_is_pristine(pheap_t heap);
#endif

#ifdef __cplusplus
}
#endif

#endif // __PHEAP_H_DEF__




