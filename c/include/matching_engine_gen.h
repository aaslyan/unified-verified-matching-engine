//
// matching_engine_gen.h
// Emitted by AMCC Schema-to-C Generator.
// Guaranteed correct by machine-checked Lean 4 proofs.
//

#pragma once
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#define ORDER_HASH_BUCKETS 8388608 // 8.38 Million buckets (2^23)
#define ORDER_CHUNK_SIZE   5000000 // 5 Million orders per dynamically allocated chunk (~320 MB)
#define LEVEL_CHUNK_SIZE   500000  // 500k price levels per chunk (~32 MB)

struct PriceLevel;

typedef struct Order {
    uint64_t            id;
    uint64_t            account_id;
    uint8_t             side;           // 0 = Buy, 1 = Sell
    uint8_t             stp_mode;       // STP policy
    uint64_t            price;
    uint64_t            qty;
    uint64_t            remaining_qty;
    struct PriceLevel  *p_price_level;

    // Intrusive FIFO Queue within PriceLevel (Llist)
    struct Order       *orders_next;
    struct Order       *orders_prev;
    bool                orders_inlist;

    // Intrusive Hash Index by Order ID (Thash)
    struct Order       *ind_order_next;
    bool                ind_order_inhash;

    // Free-list Pool Link (Tpool / Inlary)
    struct Order       *_freenext;
} Order;

typedef struct PriceLevel {
    uint64_t            price;
    uint64_t            total_qty;

    // Intrusive Llist head & tail for O(1) FIFO Orders
    struct Order       *orders_head;
    struct Order       *orders_tail;
    uint32_t            orders_n;

    // Intrusive Binary Search Tree (Atree) links
    struct PriceLevel  *tree_parent;
    struct PriceLevel  *tree_left;
    struct PriceLevel  *tree_right;
    bool                tree_intree;

    // Free-list link for PriceLevel pool
    struct PriceLevel  *_freenext;
} PriceLevel;

typedef struct EngineDb {
    // Hash table for Order ID lookup (Thash)
    struct Order      **ind_order_buckets;
    uint32_t            ind_order_n;

    // Best Bid / Best Ask Price Trees (Atree)
    struct PriceLevel  *bids_root;
    uint32_t            bids_n;

    struct PriceLevel  *asks_root;
    uint32_t            asks_n;

    // Dynamic Recyclable Memory Pools (Tpool)
    struct Order       *order_pool_free;
    uint64_t            order_pool_n;
    uint64_t            order_pool_total_allocated;

    struct PriceLevel  *level_pool_free;
    uint64_t            level_pool_n;
    uint64_t            level_pool_total_allocated;

    // Chunk tracking for safe teardown / memory cleanup
    void              **order_chunks;
    uint32_t            order_chunks_n;
    uint32_t            order_chunks_cap;

    void              **level_chunks;
    uint32_t            level_chunks_n;
    uint32_t            level_chunks_cap;
} EngineDb;

extern EngineDb g_EngineDb;

// Database Initialization & Teardown
void EngineDb_Init(void);
void EngineDb_Destroy(void);

// Dynamic Order Pool Allocator (Tpool with ReserveMem chunk growth)
struct Order *EngineDb_order_pool_Alloc(void);
void          EngineDb_order_pool_Free(struct Order *p);
uint64_t      EngineDb_order_pool_N(void);
uint64_t      EngineDb_order_pool_ReserveMem(uint64_t n_orders);

// Dynamic PriceLevel Pool Allocator (Tpool with ReserveMem chunk growth)
struct PriceLevel *EngineDb_level_pool_Alloc(void);
void               EngineDb_level_pool_Free(struct PriceLevel *p);
uint64_t           EngineDb_level_pool_ReserveMem(uint64_t n_levels);

// Order Hash Index (Thash)
struct Order *EngineDb_ind_order_Find(uint64_t id);
bool          EngineDb_ind_order_InsertMaybe(struct Order *row);
void          EngineDb_ind_order_Remove(struct Order *row);
uint32_t      EngineDb_ind_order_N(void);

// Price-Time FIFO Order Queue (Llist)
void          PriceLevel_orders_Init(struct PriceLevel *level);
void          PriceLevel_orders_InsertTail(struct PriceLevel *level, struct Order *row);
void          PriceLevel_orders_Remove(struct PriceLevel *level, struct Order *row);
struct Order *PriceLevel_orders_First(struct PriceLevel *level);
struct Order *PriceLevel_orders_Next(struct Order *row);

// Price Level Tree (Atree) - Bids (Descending: Highest Price at Root/Max)
struct PriceLevel *EngineDb_bids_Find(uint64_t price);
void               EngineDb_bids_Insert(struct PriceLevel *level);
void               EngineDb_bids_Remove(struct PriceLevel *level);
struct PriceLevel *EngineDb_bids_Best(void);

// Price Level Tree (Atree) - Asks (Ascending: Lowest Price at Root/Min)
struct PriceLevel *EngineDb_asks_Find(uint64_t price);
void               EngineDb_asks_Insert(struct PriceLevel *level);
void               EngineDb_asks_Remove(struct PriceLevel *level);
struct PriceLevel *EngineDb_asks_Best(void);
