# pheap

A portable, thread-safe private heap allocator for C/C++.

## Overview

pheap is a lightweight memory allocator library that provides private heap management with zero external dependencies. It is designed for environments where the standard allocator is unavailable or unsuitable:

- **WebAssembly** - Custom memory management for WASM modules
- **OS Development** - Kernel and bootloader memory allocation
- **Embedded Systems** - Resource-constrained environments
- **Game Engines** - Dedicated heaps for subsystems with predictable lifetimes
- **Sandboxed Applications** - Isolated memory regions

## Features

- Dynamic and fixed-size heap modes
- Thread-safe with multiple lock backends (Win32, pthread, internal spinlock)
- Executable memory allocation support
- Custom memory and lock backends
- Cross-platform: Windows, Linux, macOS, ARM, x86
- Zero external dependencies
- Drop-in malloc/free replacement
- C++ compatible

## Quick Start

```c
#include "pheap.h"

int main() {
    // Create a thread-safe heap
    pheap_t heap = pheap_create(PHEAP_FLAG_THREADSAFE);

    // Allocate memory
    void *ptr = pheap_alloc(heap, 1024);

    // Use the memory...

    // Free when done
    pheap_free(heap, ptr);

    // Destroy the heap
    pheap_destroy(heap);
    return 0;
}
```

## Installation

Add `pheap.c` and `pheap.h` to your project and compile with your existing build system.

To build as a static library:

```bash
# Linux/macOS
./build.sh

# Windows
build.bat
```

This produces `libpheap.a` (Unix) or `pheap.lib` (Windows).

## API Reference

### Heap Creation

```c
// Create a dynamic heap that grows as needed
pheap_t pheap_create(uint32_t flags);

// Create a heap within a fixed memory region (no system allocations)
pheap_t pheap_create_fixed(void *memory, size_t size, uint32_t flags);

// Create a heap with custom memory allocation callbacks
pheap_t pheap_create_custom(const pheap_alloc_config_t *config);
```

### Memory Operations

```c
// Allocate memory
void *pheap_alloc(pheap_t h, size_t size);

// Allocate zeroed memory
void *pheap_zalloc(pheap_t h, size_t size);

// Reallocate memory
void *pheap_realloc(pheap_t h, void *p, size_t size);

// Free memory
void pheap_free(pheap_t h, void *p);

// Get the size of an allocation
size_t pheap_msize(const void *p);
```

### Heap Destruction

```c
// Destroy the heap and free all memory
void pheap_destroy(pheap_t h);
```

### Global Heap Functions

When `PHEAP_USE_GLOBAL_HEAP` is enabled:

```c
void *pheap_g_alloc(size_t size);
void *pheap_g_zalloc(size_t size);
void *pheap_g_realloc(void *p, size_t size);
void pheap_g_free(void *p);
```

## Configuration Options

Configure pheap by defining these macros before including `pheap.h`. All options must be defined to a value (0 or 1), not just defined/undefined.

| Option | Default | Description |
|--------|---------|-------------|
| `PHEAP_ALIGNMENT` | `0x10` | Memory alignment (must be power of two, set to 1 for no alignment) |
| `PHEAP_PAGE_SIZE` | `0x1000` | Native page size (must be power of two) |
| `PHEAP_USE_GLOBAL_HEAP` | `0` | Enable global heap accessible anywhere |
| `PHEAP_GLOBAL_REPLACE_MALLOC` | `0` | Replace malloc/calloc/realloc/free with global heap |
| `PHEAP_INTERNAL_DEBUG` | `0` | Enable debugging support for tests |

### Lock Configuration

| Option | Value | Description |
|--------|-------|-------------|
| `PHEAP_LOCK_PRIMITIVE` | `PHEAP_NO_LOCK` (0) | Disable all locking |
| | `PHEAP_WIN32_LOCK` (1) | Use Win32 CRITICAL_SECTION |
| | `PHEAP_PTHREAD_LOCK` (2) | Use pthread_mutex_t |
| | `PHEAP_INTERNAL_LOCK` (3) | Use internal cross-platform spinlock |

Default: `PHEAP_WIN32_LOCK` on Windows, `PHEAP_PTHREAD_LOCK` elsewhere.

## Heap Flags

Pass these flags to `pheap_create()` and `pheap_create_fixed()`:

| Flag | Description |
|------|-------------|
| `PHEAP_FLAG_EXEC` | Allocate memory as executable (for JIT compilation) |
| `PHEAP_FLAG_THREADSAFE` | Enable thread-safe operations (requires locking enabled) |

## Custom Backends

### Custom Memory Allocation

Define `PHEAP_OVERRIDE_SYSTEM_HEADER` to provide custom memory primitives:

```c
#define PHEAP_OVERRIDE_SYSTEM_HEADER "my_system.h"
```

Your header must provide:

```c
// Type definitions
size_t, intNN_t, uintNN_t, intptr_t, uintptr_t

// Memory operations
void *pheap_memset(void *s, int c, size_t n);
void *pheap_memcpy(void *dest, const void *src, size_t n);

// System allocation
void *pheap_system_alloc(size_t n, int exec);
void pheap_system_free(void *p, size_t n);
```

### Custom Locking

Define `PHEAP_OVERRIDE_LOCK_HEADER` to provide custom lock primitives:

```c
#define PHEAP_OVERRIDE_LOCK_HEADER "my_locks.h"
```

Your header must provide:

```c
typedef /* your lock type */ pheap_lock_t;

void pheap_init_lock(pheap_lock_t *lock);
void pheap_uninit_lock(pheap_lock_t *lock);
void pheap_lock_lock(pheap_lock_t *lock);
void pheap_unlock_lock(pheap_lock_t *lock);
```

### Custom Allocator Callbacks

Use `pheap_create_custom()` with runtime callbacks:

```c
void *my_alloc(size_t n, void *context) {
    return my_memory_pool_alloc(context, n);
}

void my_free(void *p, size_t n, void *context) {
    my_memory_pool_free(context, p, n);
}

pheap_alloc_config_t config = {
    .custom_alloc = my_alloc,
    .custom_free = my_free,
    .context = my_pool
};

pheap_t heap = pheap_create_custom(&config);
```

## Building and Testing

### Build Scripts

```bash
# Build static library (release)
./build.sh        # Linux/macOS
build.bat         # Windows

# Build with debug symbols
DEBUG=yes ./build.sh

# Clean build artifacts
./build.sh clean
```

### Running Tests

```bash
# Run all tests
./test.sh         # Linux/macOS
test.bat          # Windows
```

### Test Environment Variables

| Variable | Description |
|----------|-------------|
| `DEBUG` | Set to `yes` for debug build with symbols |
| `TEST_SEED` | Seed for random number generator in tests |
| `NUM_TESTS` | Number of test iterations to run |

### Compiler Selection

```bash
CC=clang CXX=clang++ ./build.sh
```

## Platform Support

| Platform | Compilers | Architectures |
|----------|-----------|---------------|
| Windows | MSVC, MinGW, Clang | x86, x64, ARM64 |
| Linux | GCC, Clang | x86, x64, ARM32, ARM64 |
| macOS | Clang, GCC | x64, ARM64 |

## License

This project is released into the public domain (Unlicense). You are free to use, modify, and distribute this code without restriction.
