# About pheap
This is a C library that implements a private heap allocator, that can also be used as a replacement for malloc() in web-assembly, OS development or similar situations. It is thread-safe, performant and highly portable.

# Building pheap

## Configuration
Read through the defines in the configuration block at the top of `pheap.h` and change them according to your needs. **NOTE!** They must to be defined to a value (0 or 1 in most cases), not just defined/undefined. When you are content with the configuration, make sure to run `test.sh/test.bat`.

## Make
With overwhelming probability, the easist way is to just add `pheap.h` and `pheap.c` to your current build system and be done with it. If you absolutely need a library, you can build a static one with `build.sh` or `build.bat` depending on system.

# Current limitations
* Currently never releases memory back to the system.
* Does not utilize reserved memory where available.
* `realloc()` is just `memcpy(malloc(), old)`, which sometimes does unnecessary work.

