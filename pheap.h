#ifndef __PHEAP_H_DEF__
#define __PHEAP_H_DEF__

//
// ### Start of config ###
//
// Set the configs to 1 or 0 to override their default values
//

// PHEAP_ALIGNMENT
// Sets memory alignment. Must be a power of two.
// Set to 1 if you want no alignment.
#ifndef PHEAP_ALIGNMENT
	#define PHEAP_ALIGNMENT 0x10
#endif

// PHEAP_OVERRIDE_SYSTEM_HEADER
// Set this to the path of a header that implements all pheap system/CRT requirements.
//
// Requirements:
//   * size_t, intNN_t, uintNN_t, intptr_t, uintptr_t
//   * pheap_memset (like memset), pheap_memcpy (like memcpy)
//   * And:
//       void *pheap_system_alloc(size_t n, int exec);
//       void pheap_system_free(void *p, size_t n);
//
// #define PHEAP_OVERRIDE_SYSTEM_HEADER "pheap_system.h"

#ifdef PHEAP_OVERRIDE_SYSTEM_HEADER
    #include PHEAP_OVERRIDE_SYSTEM_HEADER

    #define PHEAP_SYSTEM_ALLOC 0
#else
    #include <stddef.h>   // size_t
    #include <stdint.h>   // uintNN_t, intNN_t
    #include <string.h>   // memset, memcpy

    #define pheap_memset  memset
    #define pheap_memcpy  memcpy

    #define PHEAP_SYSTEM_ALLOC 1
#endif

// PHEAP_OVERRIDE_LOCK_HEADER
// Set this to the path of a header that implements all pheap locking requirements.
// If unset, you can configure the internal lock used by setting PHEAP_LOCK_PRIMITIVE.
//
// Lock override header must define:
//   * pheap_lock_t - typedef of the lock primitive to use
//   * void pheap_uninit_lock(pheap_lock_t *lock);
//   * void pheap_init_lock(pheap_lock_t *lock);
//   * void pheap_lock_lock(pheap_lock_t *lock);
//   * void pheap_unlock_lock(pheap_lock_t *lock);
//
#ifdef PHEAP_OVERRIDE_LOCK_HEADER
    #include PHEAP_OVERRIDE_LOCK_HEADER
    #define PHEAP_LOCK_PRIMITIVE -1
#else
	// PHEAP_LOCK_PRIMITIVE
	// Set to one of the following:
	#define PHEAP_NO_LOCK        0  // Disables all locks
	#define PHEAP_WIN32_LOCK     1  // Uses native Win32 CRITICAL_SECTION
	#define PHEAP_PTHREAD_LOCK   2  // Uses pthread_mutex_t
	#define PHEAP_INTERNAL_LOCK  3  // Uses internal cross-platform spinlock

	#ifndef PHEAP_LOCK_PRIMITIVE
	    #ifdef _WIN32
	        #define PHEAP_LOCK_PRIMITIVE PHEAP_WIN32_LOCK
	    #else
	        #define PHEAP_LOCK_PRIMITIVE PHEAP_PTHREAD_LOCK
	    #endif
	#endif
#endif

// PHEAP_INTERNAL_DEBUG
// If tests crash or fail, enable this for debugging support.
#ifndef PHEAP_INTERNAL_DEBUG
	#define PHEAP_INTERNAL_DEBUG 0
#endif

// PHEAP_PAGE_SIZE
// Native page size. Must be a power of two.
// If unsure, leave as is.
#ifndef PHEAP_PAGE_SIZE
	#define PHEAP_PAGE_SIZE 0x1000
#endif

// PHEAP_USE_GLOBAL_HEAP
// Enables a global heap accessible anywhere.
// If locking is enabled, it will be thread-safe.
#ifndef PHEAP_USE_GLOBAL_HEAP
	#define PHEAP_USE_GLOBAL_HEAP 0
#endif

// PHEAP_GLOBAL_REPLACE_MALLOC
// If enabled, the global heap replaces malloc and related functions.
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

//
// TODO Remove this constant in version 2.0 when we add reserve+commit.
//
#ifdef PHEAP_TEST
	#define PHEAP_MEMBLOCK_SIZE_HINT 0x4000
#else
	#define PHEAP_MEMBLOCK_SIZE_HINT 32 * 0x100000
#endif

#ifdef __cplusplus
extern "C"
{
#endif

typedef struct pheap * pheap_t;

//
// Flags passed to pheap_create.
//
#define PHEAP_FLAG_EXEC 0x01 // Allocate the heap as executable.

#if PHEAP_LOCK_PRIMITIVE != PHEAP_NO_LOCK
	#define PHEAP_FLAG_THREADSAFE 0x02 // Make the heap thread-safe.
#endif


typedef void *(*pheap_mem_alloc)(size_t n, void *context);
typedef void (*pheap_mem_free)(void *p, size_t n, void *context);

typedef struct pheap_alloc_config
{
	pheap_mem_alloc custom_alloc;
	pheap_mem_free custom_free;
	void *context;
}
pheap_alloc_config_t;

pheap_t pheap_create_fixed(void *memory, size_t size, uint32_t flags);
pheap_t pheap_create(uint32_t flags);
pheap_t pheap_create_custom(const pheap_alloc_config_t *config);

void pheap_destory(pheap_t h);

void *pheap_alloc(pheap_t h, size_t size);
void *pheap_zalloc(pheap_t h, size_t size);
void *pheap_realloc(pheap_t h, void *p, size_t size);
void pheap_free(pheap_t h, void *p);

void *pheap_g_alloc(size_t size);
void *pheap_g_zalloc(size_t size);
void *pheap_g_realloc(void *p, size_t size);
void pheap_g_free(void *p);

size_t pheap_msize(const void *p);

#ifdef PHEAP_TEST
int pheap_test_is_pristine(pheap_t heap);
#endif

#ifdef __cplusplus
}
#endif

#endif // __PHEAP_H_DEF__




