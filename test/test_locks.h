#ifndef __TEST_LOCKS_H_DEF__
#define __TEST_LOCKS_H_DEF__

#ifdef _WIN32
	#include <windows.h>
    typedef CRITICAL_SECTION pheap_lock_t;
    #define pheap_lock_init(lock)   InitializeCriticalSection(lock)
    #define pheap_lock_destroy(lock) DeleteCriticalSection(lock)
    #define pheap_lock_acquire(lock)   EnterCriticalSection(lock)
    #define pheap_lock_release(lock) LeaveCriticalSection(lock)
#else
	#include <pthread.h>
    typedef pthread_mutex_t pheap_lock_t;
    #define pheap_lock_init(lock)   pthread_mutex_init(lock, NULL)
    #define pheap_lock_destroy(lock) pthread_mutex_destroy(lock)
    #define pheap_lock_acquire(lock)   pthread_mutex_lock(lock)
    #define pheap_lock_release(lock) pthread_mutex_unlock(lock)
#endif

#endif // __TEST_LOCKS_H_DEF__

