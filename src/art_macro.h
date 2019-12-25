#pragma once

#define NODE4 1
#define NODE16 2
#define NODE48 3
#define NODE256 4

#define MAX_PREFIX_LEN 10

#define IS_LEAF(x) (((uintptr_t)x & 1))
#define SET_LEAF(x) ((void*)((uintptr_t)x | 1))
#define LEAF_RAW(x) ((art_leaf*)((void*)((uintptr_t)x & ~1)))
