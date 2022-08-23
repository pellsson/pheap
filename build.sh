set -e

CC=${CC:-gcc}
CXX=${CXX:-g++}
AR=${AR:-ar}
OBJDIR=obj
CFLAGS="-Wall -Wextra -fPIE -Wno-attributes -Wno-unused-function"

TEST_DEFS="-DPHEAP_TEST -DPHEAP_USE_GLOBAL_HEAP=1"

function do_verbose() {
	echo "$1"
	$1
}

rm -fr $OBJDIR

if [ "$1" = "clean" ]; then
	exit 0
fi

if [ "$DEBUG" = "yes" ]; then
	CFLAGS="$CFLAGS -O0 -g"
else
	CFLAGS="$CFLAGS -O3"
fi

echo "Building pheap static library ($CC)"
do_verbose "mkdir -p $OBJDIR"
do_verbose "$CC $CFLAGS pheap.c -o $OBJDIR/pheap.o -c"
do_verbose "$AR crs libpheap.a $OBJDIR/pheap.o"
echo "Building pheap tests ($CXX)"
do_verbose "$CC $TEST_DEFS $CFLAGS pheap.c -o $OBJDIR/pheap-test.o -c"
do_verbose "$CXX $TEST_DEFS $CFLAGS test/test.cpp $OBJDIR/pheap-test.o -o pheap-test"

