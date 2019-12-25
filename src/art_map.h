#pragma once

#include <assert.h>
#include <emmintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>

#include <utility>

#include "art_macro.h"

namespace art_map_ns {
/**
 * This struct is included as part
 * of all the various node sizes
 */
typedef struct {
    uint8_t type;
    uint8_t num_children;
    uint32_t partial_len;
    unsigned char partial[MAX_PREFIX_LEN];
} art_node;

/**
 * Small node with only 4 children
 */
typedef struct {
    art_node n;
    unsigned char keys[4];
    art_node* children[4];
} art_node4;

/**
 * Node with 16 children
 */
typedef struct {
    art_node n;
    unsigned char keys[16];
    art_node* children[16];
} art_node16;

/**
 * Node with 48 children, but
 * a full 256 byte field.
 */
typedef struct {
    art_node n;
    unsigned char keys[256];
    art_node* children[48];
} art_node48;

/**
 * Full node with 256 children
 */
typedef struct {
    art_node n;
    art_node* children[256];
} art_node256;

/**
 * Represents a leaf. These are
 * of arbitrary size, as they include the key.
 */
typedef struct {
    size_t value;
    uint32_t key_len;
    unsigned char key[];
} art_leaf;

/**
 * Main struct, points to root.
 */
typedef struct {
    art_node* root;
    uint64_t size;
} art_tree;

inline uint64_t art_size(art_tree* t) { return t->size; }

/**
 * Allocates a node of the given type,
 * initializes to zero and sets the type.
 */
static art_node* alloc_node(uint8_t type) {
    art_node* n;
    switch (type) {
    case NODE4:
        n = (art_node*)calloc(1, sizeof(art_node4));
        break;
    case NODE16:
        n = (art_node*)calloc(1, sizeof(art_node16));
        break;
    case NODE48:
        n = (art_node*)calloc(1, sizeof(art_node48));
        break;
    case NODE256:
        n = (art_node*)calloc(1, sizeof(art_node256));
        break;
    default:
        abort();
    }
    n->type = type;
    return n;
}

/**
 * Initializes an ART tree
 * @return 0 on success.
 */
int art_tree_init(art_tree* t) {
    t->root = NULL;
    t->size = 0;
    return 0;
}

// Recursively destroys the tree
static void destroy_node(art_node* n) {
    // Break if null
    if (!n)
        return;

    // Special case leafs
    if (IS_LEAF(n)) {
        free(LEAF_RAW(n));
        return;
    }

    // Handle each node type
    int i, idx;
    union {
        art_node4* p1;
        art_node16* p2;
        art_node48* p3;
        art_node256* p4;
    } p;
    switch (n->type) {
    case NODE4:
        p.p1 = (art_node4*)n;
        for (i = 0; i < n->num_children; i++) {
            destroy_node(p.p1->children[i]);
        }
        break;

    case NODE16:
        p.p2 = (art_node16*)n;
        for (i = 0; i < n->num_children; i++) {
            destroy_node(p.p2->children[i]);
        }
        break;

    case NODE48:
        p.p3 = (art_node48*)n;
        for (i = 0; i < 256; i++) {
            idx = ((art_node48*)n)->keys[i];
            if (!idx)
                continue;
            destroy_node(p.p3->children[idx - 1]);
        }
        break;

    case NODE256:
        p.p4 = (art_node256*)n;
        for (i = 0; i < 256; i++) {
            if (p.p4->children[i])
                destroy_node(p.p4->children[i]);
        }
        break;

    default:
        abort();
    }

    // Free ourself on the way up
    free(n);
}

/**
 * Destroys an ART tree
 * @return 0 on success.
 */
int art_tree_destroy(art_tree* t) {
    destroy_node(t->root);
    return 0;
}

static art_node** find_child(art_node* n, unsigned char c) {
    int i, mask, bitfield;
    union {
        art_node4* p1;
        art_node16* p2;
        art_node48* p3;
        art_node256* p4;
    } p;
    switch (n->type) {
    case NODE4:
        p.p1 = (art_node4*)n;
        for (i = 0; i < n->num_children; i++) {
            /* this cast works around a bug in gcc 5.1 when unrolling loops
             * https://gcc.gnu.org/bugzilla/show_bug.cgi?id=59124
             */
            if (((unsigned char*)p.p1->keys)[i] == c)
                return &p.p1->children[i];
        }
        break;

        {
        case NODE16:
            p.p2 = (art_node16*)n;

// support non-86 architectures
#ifdef __i386__
            // Compare the key to all 16 stored keys
            __m128i cmp;
            cmp = _mm_cmpeq_epi8(_mm_set1_epi8(c), _mm_loadu_si128((__m128i*)p.p2->keys));

            // Use a mask to ignore children that don't exist
            mask = (1 << n->num_children) - 1;
            bitfield = _mm_movemask_epi8(cmp) & mask;
#else
#ifdef __amd64__
            // Compare the key to all 16 stored keys
            __m128i cmp;
            cmp = _mm_cmpeq_epi8(_mm_set1_epi8(c), _mm_loadu_si128((__m128i*)p.p2->keys));

            // Use a mask to ignore children that don't exist
            mask = (1 << n->num_children) - 1;
            bitfield = _mm_movemask_epi8(cmp) & mask;
#else
            // Compare the key to all 16 stored keys
            bitfield = 0;
            for (i = 0; i < 16; ++i) {
                if (p.p2->keys[i] == c)
                    bitfield |= (1 << i);
            }

            // Use a mask to ignore children that don't exist
            mask = (1 << n->num_children) - 1;
            bitfield &= mask;
#endif
#endif

            /*
             * If we have a match (any bit set) then we can
             * return the pointer match using ctz to get
             * the index.
             */
            if (bitfield)
                return &p.p2->children[__builtin_ctz(bitfield)];
            break;
        }

    case NODE48:
        p.p3 = (art_node48*)n;
        i = p.p3->keys[c];
        if (i)
            return &p.p3->children[i - 1];
        break;

    case NODE256:
        p.p4 = (art_node256*)n;
        if (p.p4->children[c])
            return &p.p4->children[c];
        break;

    default:
        abort();
    }
    return NULL;
}

// Simple inlined if
static inline int min(int a, int b) { return (a < b) ? a : b; }

/**
 * Returns the number of prefix characters shared between
 * the key and node.
 */
static int check_prefix(const art_node* n, const char* key, int key_len, int depth) {
    int max_cmp = min(min(n->partial_len, MAX_PREFIX_LEN), key_len - depth);
    int idx;
    for (idx = 0; idx < max_cmp; idx++) {
        if (n->partial[idx] != key[depth + idx])
            return idx;
    }
    return idx;
}

/**
 * Checks if a leaf matches
 * @return 0 on success.
 */
static int leaf_matches(const art_leaf* n, const char* key, int key_len, int depth) {
    (void)depth;
    // Fail if the key lengths are different
    if (n->key_len != (uint32_t)key_len)
        return 1;

    // Compare the keys starting at the depth
    return memcmp(n->key, key, key_len);
}

/**
 * Searches for a value in the ART tree
 * @arg t The tree
 * @arg key The key
 * @arg key_len The length of the key
 * @return NULL if the item was not found, otherwise
 * the value pointer is returned.
 */
size_t* art_search(const art_tree* t, const char* key, int key_len) {
    art_node** child;
    art_node* n = t->root;
    int prefix_len, depth = 0;
    while (n) {
        // Might be a leaf
        if (IS_LEAF(n)) {
            n = (art_node*)LEAF_RAW(n);
            // Check if the expanded path matches
            if (!leaf_matches((art_leaf*)n, key, key_len, depth)) {
                return &((art_leaf*)n)->value;
            }
            return NULL;
        }

        // Bail if the prefix does not match
        if (n->partial_len) {
            prefix_len = check_prefix(n, key, key_len, depth);
            if (prefix_len != min(MAX_PREFIX_LEN, n->partial_len))
                return NULL;
            depth = depth + n->partial_len;
        }

        // Recursively search
        child = find_child(n, key[depth]);
        n = (child) ? *child : NULL;
        depth++;
    }
    return NULL;
}

static art_leaf* make_leaf(const char* key, int key_len, size_t value) {
    art_leaf* l = (art_leaf*)calloc(1, sizeof(art_leaf) + key_len);
    l->value = value;
    l->key_len = key_len;
    memcpy(l->key, key, key_len);
    return l;
}

static int longest_common_prefix(art_leaf* l1, art_leaf* l2, int depth) {
    int max_cmp = min(l1->key_len, l2->key_len) - depth;
    int idx;
    for (idx = 0; idx < max_cmp; idx++) {
        if (l1->key[depth + idx] != l2->key[depth + idx])
            return idx;
    }
    return idx;
}

static void copy_header(art_node* dest, art_node* src) {
    dest->num_children = src->num_children;
    dest->partial_len = src->partial_len;
    memcpy(dest->partial, src->partial, min(MAX_PREFIX_LEN, src->partial_len));
}

static void add_child256(art_node256* n, art_node** ref, unsigned char c, void* child) {
    (void)ref;
    n->n.num_children++;
    n->children[c] = (art_node*)child;
}

static void add_child48(art_node48* n, art_node** ref, unsigned char c, void* child) {
    if (n->n.num_children < 48) {
        int pos = 0;
        while (n->children[pos])
            pos++;
        n->children[pos] = (art_node*)child;
        n->keys[c] = pos + 1;
        n->n.num_children++;
    } else {
        art_node256* new_node = (art_node256*)alloc_node(NODE256);
        for (int i = 0; i < 256; i++) {
            if (n->keys[i]) {
                new_node->children[i] = n->children[n->keys[i] - 1];
            }
        }
        copy_header((art_node*)new_node, (art_node*)n);
        *ref = (art_node*)new_node;
        free(n);
        add_child256(new_node, ref, c, child);
    }
}

static void add_child16(art_node16* n, art_node** ref, unsigned char c, void* child) {
    if (n->n.num_children < 16) {
        unsigned mask = (1 << n->n.num_children) - 1;

// support non-x86 architectures
#ifdef __i386__
        __m128i cmp;

        // Compare the key to all 16 stored keys
        cmp = _mm_cmplt_epi8(_mm_set1_epi8(c), _mm_loadu_si128((__m128i*)n->keys));

        // Use a mask to ignore children that don't exist
        unsigned bitfield = _mm_movemask_epi8(cmp) & mask;
#else
#ifdef __amd64__
        __m128i cmp;

        // Compare the key to all 16 stored keys
        cmp = _mm_cmplt_epi8(_mm_set1_epi8(c), _mm_loadu_si128((__m128i*)n->keys));

        // Use a mask to ignore children that don't exist
        unsigned bitfield = _mm_movemask_epi8(cmp) & mask;
#else
        // Compare the key to all 16 stored keys
        unsigned bitfield = 0;
        for (short i = 0; i < 16; ++i) {
            if (c < n->keys[i])
                bitfield |= (1 << i);
        }

        // Use a mask to ignore children that don't exist
        bitfield &= mask;
#endif
#endif

        // Check if less than any
        unsigned idx;
        if (bitfield) {
            idx = __builtin_ctz(bitfield);
            memmove(n->keys + idx + 1, n->keys + idx, n->n.num_children - idx);
            memmove(n->children + idx + 1, n->children + idx,
                (n->n.num_children - idx) * sizeof(void*));
        } else
            idx = n->n.num_children;

        // Set the child
        n->keys[idx] = c;
        n->children[idx] = (art_node*)child;
        n->n.num_children++;

    } else {
        art_node48* new_node = (art_node48*)alloc_node(NODE48);

        // Copy the child pointers and populate the key map
        memcpy(new_node->children, n->children, sizeof(void*) * n->n.num_children);
        for (int i = 0; i < n->n.num_children; i++) {
            new_node->keys[n->keys[i]] = i + 1;
        }
        copy_header((art_node*)new_node, (art_node*)n);
        *ref = (art_node*)new_node;
        free(n);
        add_child48(new_node, ref, c, child);
    }
}

static void add_child4(art_node4* n, art_node** ref, unsigned char c, void* child) {
    if (n->n.num_children < 4) {
        int idx;
        for (idx = 0; idx < n->n.num_children; idx++) {
            if (c < n->keys[idx])
                break;
        }

        // Shift to make room
        memmove(n->keys + idx + 1, n->keys + idx, n->n.num_children - idx);
        memmove(
            n->children + idx + 1, n->children + idx, (n->n.num_children - idx) * sizeof(void*));

        // Insert element
        n->keys[idx] = c;
        n->children[idx] = (art_node*)child;
        n->n.num_children++;

    } else {
        art_node16* new_node = (art_node16*)alloc_node(NODE16);

        // Copy the child pointers and the key map
        memcpy(new_node->children, n->children, sizeof(void*) * n->n.num_children);
        memcpy(new_node->keys, n->keys, sizeof(unsigned char) * n->n.num_children);
        copy_header((art_node*)new_node, (art_node*)n);
        *ref = (art_node*)new_node;
        free(n);
        add_child16(new_node, ref, c, child);
    }
}

static void add_child(art_node* n, art_node** ref, unsigned char c, void* child) {
    switch (n->type) {
    case NODE4:
        return add_child4((art_node4*)n, ref, c, child);
    case NODE16:
        return add_child16((art_node16*)n, ref, c, child);
    case NODE48:
        return add_child48((art_node48*)n, ref, c, child);
    case NODE256:
        return add_child256((art_node256*)n, ref, c, child);
    default:
        abort();
    }
}

// Find the minimum leaf under a node
static art_leaf* minimum(const art_node* n) {
    // Handle base cases
    if (!n)
        return NULL;
    if (IS_LEAF(n))
        return LEAF_RAW(n);

    int idx;
    switch (n->type) {
    case NODE4:
        return minimum(((const art_node4*)n)->children[0]);
    case NODE16:
        return minimum(((const art_node16*)n)->children[0]);
    case NODE48:
        idx = 0;
        while (!((const art_node48*)n)->keys[idx])
            idx++;
        idx = ((const art_node48*)n)->keys[idx] - 1;
        return minimum(((const art_node48*)n)->children[idx]);
    case NODE256:
        idx = 0;
        while (!((const art_node256*)n)->children[idx])
            idx++;
        return minimum(((const art_node256*)n)->children[idx]);
    default:
        abort();
    }
}

/**
 * Calculates the index at which the prefixes mismatch
 */
static int prefix_mismatch(const art_node* n, const char* key, int key_len, int depth) {
    int max_cmp = min(min(MAX_PREFIX_LEN, n->partial_len), key_len - depth);
    int idx;
    for (idx = 0; idx < max_cmp; idx++) {
        if (n->partial[idx] != key[depth + idx])
            return idx;
    }

    // If the prefix is short we can avoid finding a leaf
    if (n->partial_len > MAX_PREFIX_LEN) {
        // Prefix is longer than what we've checked, find a leaf
        art_leaf* l = minimum(n);
        max_cmp = min(l->key_len, key_len) - depth;
        for (; idx < max_cmp; idx++) {
            if (l->key[idx + depth] != key[depth + idx])
                return idx;
        }
    }
    return idx;
}

static size_t* recursive_insert(
    art_node* n, art_node** ref, const char* key, int key_len, size_t value, int depth, int* old) {
    // If we are at a NULL node, inject a leaf
    if (!n) {
        art_leaf* l = make_leaf(key, key_len, value);
        *ref = (art_node*)SET_LEAF(l);
        return &l->value;
    }

    // If we are at a leaf, we need to replace it with a node
    if (IS_LEAF(n)) {
        art_leaf* l = LEAF_RAW(n);

        // Check if we are updating an existing value
        if (!leaf_matches(l, key, key_len, depth)) {
            *old = 1;
            return &l->value;
        }

        // New value, we must split the leaf into a node4
        art_node4* new_node = (art_node4*)alloc_node(NODE4);

        // Create a new leaf
        art_leaf* l2 = make_leaf(key, key_len, value);

        // Determine longest prefix
        int longest_prefix = longest_common_prefix(l, l2, depth);
        new_node->n.partial_len = longest_prefix;
        memcpy(new_node->n.partial, key + depth, min(MAX_PREFIX_LEN, longest_prefix));
        // Add the leafs to the new node4
        *ref = (art_node*)new_node;
        add_child4(new_node, ref, l->key[depth + longest_prefix], SET_LEAF(l));
        add_child4(new_node, ref, l2->key[depth + longest_prefix], SET_LEAF(l2));
        return &l2->value;
    }

    // Check if given node has a prefix
    if (n->partial_len) {
        // Determine if the prefixes differ, since we need to split
        int prefix_diff = prefix_mismatch(n, key, key_len, depth);
        if ((uint32_t)prefix_diff >= n->partial_len) {
            depth += n->partial_len;
            goto RECURSE_SEARCH;
        }

        // Create a new node
        art_node4* new_node = (art_node4*)alloc_node(NODE4);
        *ref = (art_node*)new_node;
        new_node->n.partial_len = prefix_diff;
        memcpy(new_node->n.partial, n->partial, min(MAX_PREFIX_LEN, prefix_diff));

        // Adjust the prefix of the old node
        if (n->partial_len <= MAX_PREFIX_LEN) {
            add_child4(new_node, ref, n->partial[prefix_diff], n);
            n->partial_len -= (prefix_diff + 1);
            memmove(n->partial, n->partial + prefix_diff + 1, min(MAX_PREFIX_LEN, n->partial_len));
        } else {
            n->partial_len -= (prefix_diff + 1);
            art_leaf* l = minimum(n);
            add_child4(new_node, ref, l->key[depth + prefix_diff], n);
            memcpy(
                n->partial, l->key + depth + prefix_diff + 1, min(MAX_PREFIX_LEN, n->partial_len));
        }

        // Insert the new leaf
        art_leaf* l = make_leaf(key, key_len, value);
        add_child4(new_node, ref, key[depth + prefix_diff], SET_LEAF(l));
        return &l->value;
    }

RECURSE_SEARCH:;

    // Find a child to recurse to
    art_node** child = find_child(n, key[depth]);
    if (child) {
        return recursive_insert(*child, child, key, key_len, value, depth + 1, old);
    }

    // No child, node goes within us
    art_leaf* l = make_leaf(key, key_len, value);
    add_child(n, ref, key[depth], SET_LEAF(l));
    return &l->value;
}

std::pair<size_t*, bool> art_insert(art_tree* t, const char* key, int key_len, size_t value) {
    int old_val = 0;
    size_t* old = recursive_insert(t->root, &t->root, key, key_len, value, 0, &old_val);
    if (!old_val)
        t->size++;
    return std::make_pair(old, !old_val);
}
}

class art_map {
    art_map_ns::art_tree root;

public:
    art_map() { art_map_ns::art_tree_init(&root); }
    ~art_map() { art_map_ns::art_tree_destroy(&root); }
    std::pair<size_t*, bool> emplace(const char* p, size_t len, size_t v) {
        return art_map_ns::art_insert(&root, p, len, v);
    }
    size_t* find(const char* p, size_t len) { return art_map_ns::art_search(&root, p, len); }
    size_t bucket_count() { return 0; }
};

/* Local Variables:  */
/* mode: c++         */
/* comment-column: 0 */
/* End:              */
