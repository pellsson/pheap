set -e
DEBUG=yes ./build.sh && ./pheap-test && ./pheap-test-ext && ./pheap-test-tcache
