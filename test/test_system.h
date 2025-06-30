#ifndef __TEST_SYSTEM_H_DEF__
#define __TEST_SYSTEM_H_DEF__

#include <stdint.h>
#include <stddef.h>
#include <string.h>

#define pheap_memset memset
#define pheap_memcpy memcpy

#ifdef _WIN32
#include <windows.h>

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
        __asm__("int3");
    }
}
 
#else

#include <sys/mman.h>
    
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
        __asm__("int3");
    }
}

#endif

#endif // __TEST_SYSTEM_H_DEF__

