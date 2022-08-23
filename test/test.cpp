#include "../pheap.h"

#include <stdio.h>
#include <stdlib.h>

#include <thread>

#include <vector>
#include <algorithm>
#include <array>
#include <iostream>

#include <unordered_set>

#define test_cmp(lhs, rhs, op) \
{ \
	auto rv = (rhs); \
	auto lv = (lhs); \
	if(!(rv op lv)) \
	{ \
		std::cout << "FAILS (Line: " << __LINE__ << "): " << #lhs " " #op " " #rhs << std::endl; \
		std::cout << "LHS " << (lv) << ", RHS " << (rv) << std::endl; \
		exit(1); \
	} \
}

#define test_eq(lhs, rhs)	test_cmp((lhs), (rhs), ==)
#define test_neq(lhs, rhs)	test_cmp((lhs), (rhs), !=)
#define test_true(x)		test_eq(x, true)
#define test_not_null(x)	test_neq(static_cast<void *>(x), static_cast<void *>(nullptr))
#define test_null(x)		test_eq(static_cast<void *>(x), static_cast<void *>(nullptr))

size_t rand_between(size_t low, size_t high)
{
	return rand() % (high - low + 1);
}

static void test_alloc_free(pheap_t h, uint32_t seed)
{
	std::array<void *, 7> allocs{};
	std::array<uint32_t, 7> free_order{0,1,2,3,4,5,6};
	std::array<std::pair<uint32_t, uint32_t>, 7> size_range{
		std::make_pair(0x00, 0x0F),
		std::make_pair(0x20, 0x3F), 
		std::make_pair(0x40, 0x7F),
		std::make_pair(0x80, 0xFF),
		std::make_pair(0x100, 0x200),
		std::make_pair(0x0, 0x1000),
	};
	

	do
	{
		srand(seed);
		test_true((bool)pheap_test_is_pristine(h));

		for(size_t i = 0; i < allocs.size(); ++i)
		{
			const auto &r = size_range[i];
			size_t n = rand_between(r.first, r.second);
			void *p = pheap_alloc(h, n);
			test_not_null(p);
			memset(p, 'a', n);
			test_true(n == pheap_msize(p));
			if(allocs[i])
			{
				test_eq(p, allocs[i]);
			}
			allocs[i] = p;
		}

		for(size_t i = 0; i < allocs.size(); ++i)
		{
			pheap_free(h, allocs[free_order[i]]);
		}
		
		test_true((bool)pheap_test_is_pristine(h));
	}
	while(std::next_permutation(free_order.begin(), free_order.end()));
}

static void test_many_pools(pheap_t h)
{
	int32_t n_bytes = 0;

	std::vector<std::pair<void *, int32_t>> allocs;

	for(int i = 0; i < 2000; ++i)
	{
		int32_t n = 0;
		size_t action = rand_between(0, 10);

		if(n_bytes >= (0x20 * PHEAP_MEMBLOCK_SIZE_HINT))
		{
			printf("Terminating due to memory (this is fine)...\n");
			break;
		}

		if(action < 5)
		{
			if(allocs.size())
			{
				auto &alloc = allocs[0];

				// printf("Free %p (%d)\n", alloc.first, alloc.second);

				n = (int32_t)pheap_msize(alloc.first);

				if(n != alloc.second)
				{
					n = n;
				}

				test_true(n == alloc.second);
				pheap_free(h, alloc.first);
				n *= -1;

				allocs.erase(allocs.begin());
			}
			else
			{
				test_true((bool)pheap_test_is_pristine(h));
			}
		}
		else if(action < 8)
		{
			n = (int32_t)rand_between(0, 0x100);
		}
		else
		{
			n = (int32_t)rand_between(0x100, PHEAP_MEMBLOCK_SIZE_HINT / 8);
		}

		n_bytes += n;

		if(n_bytes < 0)
		{
			n = n;
		}

		test_true(n_bytes >= 0);

		if(n >= 0)
		{
			void *p = pheap_alloc(h, n);
			// printf("Alloc %p (%d)\n", p, n);
			test_not_null(p);
			test_true((size_t)n == pheap_msize(p));
			memset(p, 'A', n);
			allocs.push_back(std::make_pair(p, (int32_t)n));
		}
	}

	for(auto &r : allocs)
	{
		test_true((size_t)r.second == pheap_msize(r.first));
		pheap_free(h, r.first);
	}

	test_true((bool)pheap_test_is_pristine(h));
}

int main()
{
#ifdef PHEAP_FLAG_THREADSAFE
	uint32_t flags = PHEAP_FLAG_THREADSAFE;
#else
	uint32_t flags = 0;
#endif
	pheap_t heap = pheap_create(flags);
	uint32_t n = (uint32_t)time(0);

	if(getenv("TEST_SEED"))
	{
		n = atoi(getenv("TEST_SEED"));
	}

	printf("Testing with random seed: %d\n", n);

	srand(n);

	pheap_free(heap, nullptr);

	printf("Testing huge allocations...\n");
	void *a = pheap_alloc(heap, 0x10000000);
	void *b = pheap_alloc(heap, 0x10000000);
	void *c = pheap_alloc(heap, 0x10000000);

	test_true(!pheap_test_is_pristine(heap));
	pheap_free(heap, b);
	test_true(!pheap_test_is_pristine(heap));
	pheap_free(heap, c);
	test_true(!pheap_test_is_pristine(heap));
	pheap_free(heap, a);
	test_true((bool)pheap_test_is_pristine(heap));

	printf("Testing variations of alloc vs. free order...\n");
	for(uint32_t i = 0; i < 0x100; ++i)
	{
		test_alloc_free(heap, rand() + i);
	}

	printf("Testing a lot of memory pools...\n");
	for(uint32_t i = 0; i < 0x800; ++i)
	{
		test_many_pools(heap);
	}

#ifdef PHEAP_FLAG_THREADSAFE
	std::vector<std::thread> threads;
	printf("Testing concurrent allocations against same heap...\n");
	for(uint32_t i = 0; i < 64; ++i)
	{
		threads.push_back(std::thread([i, heap]()
		{
			for(uint32_t x = 0; x < 0x8000; ++x)
			{
				size_t n = rand() % 0x2000;
				void *p = pheap_alloc(heap, n);
				test_true(p != nullptr);
				memset(p, i, n);
				test_true(n == pheap_msize(p));
				pheap_free(heap, p);
			}
		}));
	}

	for(auto &t : threads)
	{
		t.join();
	}

	test_true((bool)pheap_test_is_pristine(heap));
#endif

	printf("Destroying heap...\n");
	pheap_destory(heap);

#if PHEAP_USE_GLOBAL_HEAP != 0
	printf("Testing global heap...\n");
	void *p = pheap_g_alloc(0x1000);
	test_true(PHEAP_NULL != p);
	pheap_g_free(p);
	void *q = pheap_g_alloc(0x1000);
	test_true(p == q);
	pheap_g_free(q);
#endif

	printf("Test successful!\n");

	return 0;
}


