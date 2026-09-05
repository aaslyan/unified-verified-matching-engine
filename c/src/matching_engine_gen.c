//
// matching_engine_gen.c
// Implementation of AMCC generated structures with dynamic chunk-based Tpool.
//

#include "../include/matching_engine_gen.h"
#include <stdlib.h>
#include <string.h>

EngineDb g_EngineDb;

static void track_order_chunk(void *chunk) {
    if (g_EngineDb.order_chunks_n >= g_EngineDb.order_chunks_cap) {
        uint32_t new_cap = g_EngineDb.order_chunks_cap == 0 ? 16 : g_EngineDb.order_chunks_cap * 2;
        void **new_arr = (void **)realloc(g_EngineDb.order_chunks, new_cap * sizeof(void *));
        if (!new_arr) return;
        g_EngineDb.order_chunks = new_arr;
        g_EngineDb.order_chunks_cap = new_cap;
    }
    g_EngineDb.order_chunks[g_EngineDb.order_chunks_n++] = chunk;
}

static void track_level_chunk(void *chunk) {
    if (g_EngineDb.level_chunks_n >= g_EngineDb.level_chunks_cap) {
        uint32_t new_cap = g_EngineDb.level_chunks_cap == 0 ? 16 : g_EngineDb.level_chunks_cap * 2;
        void **new_arr = (void **)realloc(g_EngineDb.level_chunks, new_cap * sizeof(void *));
        if (!new_arr) return;
        g_EngineDb.level_chunks = new_arr;
        g_EngineDb.level_chunks_cap = new_cap;
    }
    g_EngineDb.level_chunks[g_EngineDb.level_chunks_n++] = chunk;
}

// Dynamic Order Chunk Allocation (ReserveMem)
uint64_t EngineDb_order_pool_ReserveMem(uint64_t n_orders) {
    if (n_orders == 0) return 0;
    struct Order *chunk = (struct Order *)calloc(n_orders, sizeof(struct Order));
    if (!chunk) return 0;
    track_order_chunk(chunk);

    for (uint64_t i = 0; i < n_orders; ++i) {
        chunk[i]._freenext = g_EngineDb.order_pool_free;
        g_EngineDb.order_pool_free = &chunk[i];
    }
    g_EngineDb.order_pool_total_allocated += n_orders;
    return n_orders;
}

// Dynamic PriceLevel Chunk Allocation (ReserveMem)
uint64_t EngineDb_level_pool_ReserveMem(uint64_t n_levels) {
    if (n_levels == 0) return 0;
    struct PriceLevel *chunk = (struct PriceLevel *)calloc(n_levels, sizeof(struct PriceLevel));
    if (!chunk) return 0;
    track_level_chunk(chunk);

    for (uint64_t i = 0; i < n_levels; ++i) {
        chunk[i]._freenext = g_EngineDb.level_pool_free;
        g_EngineDb.level_pool_free = &chunk[i];
    }
    g_EngineDb.level_pool_total_allocated += n_levels;
    return n_levels;
}

void EngineDb_Destroy(void) {
    if (g_EngineDb.ind_order_buckets) {
        free(g_EngineDb.ind_order_buckets);
        g_EngineDb.ind_order_buckets = NULL;
    }
    if (g_EngineDb.order_chunks) {
        for (uint32_t i = 0; i < g_EngineDb.order_chunks_n; ++i) {
            free(g_EngineDb.order_chunks[i]);
        }
        free(g_EngineDb.order_chunks);
        g_EngineDb.order_chunks = NULL;
    }
    if (g_EngineDb.level_chunks) {
        for (uint32_t i = 0; i < g_EngineDb.level_chunks_n; ++i) {
            free(g_EngineDb.level_chunks[i]);
        }
        free(g_EngineDb.level_chunks);
        g_EngineDb.level_chunks = NULL;
    }
    memset(&g_EngineDb, 0, sizeof(EngineDb));
}

void EngineDb_Init(void) {
    EngineDb_Destroy();

    // 1. Allocate 8.38M hash buckets
    g_EngineDb.ind_order_buckets = (struct Order **)calloc(ORDER_HASH_BUCKETS, sizeof(struct Order *));

    // 2. Pre-allocate initial Order & Level chunks
    EngineDb_order_pool_ReserveMem(ORDER_CHUNK_SIZE);
    EngineDb_level_pool_ReserveMem(LEVEL_CHUNK_SIZE);

    g_EngineDb.bids_root = NULL;
    g_EngineDb.bids_n = 0;
    g_EngineDb.asks_root = NULL;
    g_EngineDb.asks_n = 0;
    g_EngineDb.ind_order_n = 0;
}

// -------------------------------------------------------------
// Order Pool Allocator (Fixed Pre-Allocated Tpool)
// -------------------------------------------------------------
struct Order *EngineDb_order_pool_Alloc(void) {
    struct Order *p = g_EngineDb.order_pool_free;
    if (p != NULL) {
        g_EngineDb.order_pool_free = p->_freenext;
        p->_freenext = NULL;
        p->orders_next = NULL;
        p->orders_prev = NULL;
        p->orders_inlist = false;
        p->ind_order_next = NULL;
        p->ind_order_inhash = false;
        g_EngineDb.order_pool_n++;
    }
    return p;
}

void EngineDb_order_pool_Free(struct Order *p) {
    if (p != NULL) {
        p->_freenext = g_EngineDb.order_pool_free;
        g_EngineDb.order_pool_free = p;
        if (g_EngineDb.order_pool_n > 0) {
            g_EngineDb.order_pool_n--;
        }
    }
}

uint64_t EngineDb_order_pool_N(void) {
    return g_EngineDb.order_pool_n;
}

// -------------------------------------------------------------
// PriceLevel Pool Allocator (Fixed Pre-Allocated Tpool)
// -------------------------------------------------------------
struct PriceLevel *EngineDb_level_pool_Alloc(void) {
    struct PriceLevel *p = g_EngineDb.level_pool_free;
    if (p != NULL) {
        g_EngineDb.level_pool_free = p->_freenext;
        p->_freenext = NULL;
        p->orders_head = NULL;
        p->orders_tail = NULL;
        p->orders_n = 0;
        p->total_qty = 0;
        p->tree_parent = NULL;
        p->tree_left = NULL;
        p->tree_right = NULL;
        p->tree_intree = false;
        g_EngineDb.level_pool_n++;
    }
    return p;
}

void EngineDb_level_pool_Free(struct PriceLevel *p) {
    if (p != NULL) {
        p->_freenext = g_EngineDb.level_pool_free;
        g_EngineDb.level_pool_free = p;
        if (g_EngineDb.level_pool_n > 0) {
            g_EngineDb.level_pool_n--;
        }
    }
}

// -------------------------------------------------------------
// Order Hash Index (Thash)
// -------------------------------------------------------------
static inline uint32_t hash_order_id(uint64_t id) {
    return (uint32_t)(id & (ORDER_HASH_BUCKETS - 1));
}

struct Order *EngineDb_ind_order_Find(uint64_t id) {
    uint32_t b = hash_order_id(id);
    struct Order *p = g_EngineDb.ind_order_buckets[b];
    while (p != NULL) {
        if (p->id == id) {
            return p;
        }
        p = p->ind_order_next;
    }
    return NULL;
}

bool EngineDb_ind_order_InsertMaybe(struct Order *row) {
    if (row == NULL || row->ind_order_inhash) {
        return false;
    }
    if (EngineDb_ind_order_Find(row->id) != NULL) {
        return false; // Key already exists
    }
    uint32_t b = hash_order_id(row->id);
    row->ind_order_next = g_EngineDb.ind_order_buckets[b];
    g_EngineDb.ind_order_buckets[b] = row;
    row->ind_order_inhash = true;
    g_EngineDb.ind_order_n++;
    return true;
}

void EngineDb_ind_order_Remove(struct Order *row) {
    if (row == NULL || !row->ind_order_inhash) {
        return;
    }
    uint32_t b = hash_order_id(row->id);
    struct Order *cur = g_EngineDb.ind_order_buckets[b];
    struct Order *prev = NULL;
    while (cur != NULL) {
        if (cur == row) {
            if (prev != NULL) {
                prev->ind_order_next = cur->ind_order_next;
            } else {
                g_EngineDb.ind_order_buckets[b] = cur->ind_order_next;
            }
            cur->ind_order_next = NULL;
            cur->ind_order_inhash = false;
            g_EngineDb.ind_order_n--;
            return;
        }
        prev = cur;
        cur = cur->ind_order_next;
    }
}

uint32_t EngineDb_ind_order_N(void) {
    return g_EngineDb.ind_order_n;
}

// -------------------------------------------------------------
// FIFO Order Queue within PriceLevel (Llist)
// -------------------------------------------------------------
void PriceLevel_orders_Init(struct PriceLevel *level) {
    if (level) {
        level->orders_head = NULL;
        level->orders_tail = NULL;
        level->orders_n = 0;
        level->total_qty = 0;
    }
}

void PriceLevel_orders_InsertTail(struct PriceLevel *level, struct Order *row) {
    if (!level || !row || row->orders_inlist) return;

    row->orders_next = NULL;
    row->orders_prev = level->orders_tail;
    row->p_price_level = level;
    if (level->orders_tail != NULL) {
        level->orders_tail->orders_next = row;
    } else {
        level->orders_head = row;
    }
    level->orders_tail = row;
    row->orders_inlist = true;
    level->orders_n++;
    level->total_qty += row->remaining_qty;
}

void PriceLevel_orders_Remove(struct PriceLevel *level, struct Order *row) {
    if (!level || !row || !row->orders_inlist) return;

    if (row->orders_prev != NULL) {
        row->orders_prev->orders_next = row->orders_next;
    } else {
        level->orders_head = row->orders_next;
    }
    if (row->orders_next != NULL) {
        row->orders_next->orders_prev = row->orders_prev;
    } else {
        level->orders_tail = row->orders_prev;
    }

    row->orders_next = NULL;
    row->orders_prev = NULL;
    row->orders_inlist = false;
    row->p_price_level = NULL;

    if (level->orders_n > 0) level->orders_n--;
    if (level->total_qty >= row->remaining_qty) {
        level->total_qty -= row->remaining_qty;
    } else {
        level->total_qty = 0;
    }
}

struct Order *PriceLevel_orders_First(struct PriceLevel *level) {
    return level ? level->orders_head : NULL;
}

struct Order *PriceLevel_orders_Next(struct Order *row) {
    return row ? row->orders_next : NULL;
}

// -------------------------------------------------------------
// Price Level Search Trees (Atree)
// -------------------------------------------------------------
static struct PriceLevel *tree_find(struct PriceLevel *root, uint64_t price) {
    struct PriceLevel *cur = root;
    while (cur != NULL) {
        if (price == cur->price) return cur;
        if (price < cur->price) cur = cur->tree_left;
        else cur = cur->tree_right;
    }
    return NULL;
}

static void tree_insert(struct PriceLevel **root_ptr, struct PriceLevel *node) {
    if (!root_ptr || !node) return;
    node->tree_left = NULL;
    node->tree_right = NULL;
    node->tree_parent = NULL;
    node->tree_intree = true;

    if (*root_ptr == NULL) {
        *root_ptr = node;
        return;
    }

    struct PriceLevel *cur = *root_ptr;
    struct PriceLevel *parent = NULL;
    while (cur != NULL) {
        parent = cur;
        if (node->price < cur->price) {
            cur = cur->tree_left;
        } else {
            cur = cur->tree_right;
        }
    }

    node->tree_parent = parent;
    if (node->price < parent->price) {
        parent->tree_left = node;
    } else {
        parent->tree_right = node;
    }
}

static void tree_remove(struct PriceLevel **root_ptr, struct PriceLevel *node) {
    if (!root_ptr || !node || !node->tree_intree) return;

    if (node->tree_left == NULL) {
        struct PriceLevel *r = node->tree_right;
        if (node->tree_parent != NULL) {
            if (node->tree_parent->tree_left == node) node->tree_parent->tree_left = r;
            else node->tree_parent->tree_right = r;
        } else {
            *root_ptr = r;
        }
        if (r != NULL) r->tree_parent = node->tree_parent;
    } else if (node->tree_right == NULL) {
        struct PriceLevel *l = node->tree_left;
        if (node->tree_parent != NULL) {
            if (node->tree_parent->tree_left == node) node->tree_parent->tree_left = l;
            else node->tree_parent->tree_right = l;
        } else {
            *root_ptr = l;
        }
        if (l != NULL) l->tree_parent = node->tree_parent;
    } else {
        // Successor swap
        struct PriceLevel *succ = node->tree_right;
        while (succ->tree_left != NULL) succ = succ->tree_left;

        if (succ->tree_parent != node) {
            if (succ->tree_parent->tree_left == succ) succ->tree_parent->tree_left = succ->tree_right;
            else succ->tree_parent->tree_right = succ->tree_right;
            if (succ->tree_right != NULL) succ->tree_right->tree_parent = succ->tree_parent;

            succ->tree_right = node->tree_right;
            if (succ->tree_right != NULL) succ->tree_right->tree_parent = succ;
        }

        if (node->tree_parent != NULL) {
            if (node->tree_parent->tree_left == node) node->tree_parent->tree_left = succ;
            else node->tree_parent->tree_right = succ;
        } else {
            *root_ptr = succ;
        }
        succ->tree_parent = node->tree_parent;
        succ->tree_left = node->tree_left;
        if (succ->tree_left != NULL) succ->tree_left->tree_parent = succ;
    }

    node->tree_left = NULL;
    node->tree_right = NULL;
    node->tree_parent = NULL;
    node->tree_intree = false;
}

// Bids Tree (Best bid is maximum price)
struct PriceLevel *EngineDb_bids_Find(uint64_t price) {
    return tree_find(g_EngineDb.bids_root, price);
}

void EngineDb_bids_Insert(struct PriceLevel *level) {
    tree_insert(&g_EngineDb.bids_root, level);
    g_EngineDb.bids_n++;
}

void EngineDb_bids_Remove(struct PriceLevel *level) {
    tree_remove(&g_EngineDb.bids_root, level);
    if (g_EngineDb.bids_n > 0) g_EngineDb.bids_n--;
}

struct PriceLevel *EngineDb_bids_Best(void) {
    struct PriceLevel *cur = g_EngineDb.bids_root;
    if (!cur) return NULL;
    while (cur->tree_right != NULL) {
        cur = cur->tree_right; // Max price for bids
    }
    return cur;
}

// Asks Tree (Best ask is minimum price)
struct PriceLevel *EngineDb_asks_Find(uint64_t price) {
    return tree_find(g_EngineDb.asks_root, price);
}

void EngineDb_asks_Insert(struct PriceLevel *level) {
    tree_insert(&g_EngineDb.asks_root, level);
    g_EngineDb.asks_n++;
}

void EngineDb_asks_Remove(struct PriceLevel *level) {
    tree_remove(&g_EngineDb.asks_root, level);
    if (g_EngineDb.asks_n > 0) g_EngineDb.asks_n--;
}

struct PriceLevel *EngineDb_asks_Best(void) {
    struct PriceLevel *cur = g_EngineDb.asks_root;
    if (!cur) return NULL;
    while (cur->tree_left != NULL) {
        cur = cur->tree_left; // Min price for asks
    }
    return cur;
}
