/*
 * engine_db_adapter.c — engine_db.h implemented on the handwritten data layer.
 *
 * Below the line of plan v2 §3: this file is trusted, and Phase 5 tests it
 * (as linked with the data layer) against the EngineDb contract laws.
 *
 * What it maintains beyond forwarding calls:
 *   - Capacity. ME_order_alloc / ME_level_alloc return NULL exactly when
 *     order_pool_n / level_pool_n has reached ME_capacity(), whatever the
 *     underlying pools reserved. ME_adapter_init reserves at least that many
 *     rows in each pool, so an allocation below capacity never fails.
 *   - Level totals. PriceLevel.total_qty is not in the contract. The data
 *     layer's InsertTail/Remove add and subtract an order's remaining
 *     quantity; ME_order_set_remaining adjusts the owner level's total by the
 *     difference, so total_qty stays the sum of its orders' remaining
 *     quantities, which MatchingEngine_CheckInvariants checks.
 *   - Widened fields. Order.side and Order.stp_mode are uint64_t in the data
 *     layer (edit to matching_engine_gen.h), so reads and writes are exact.
 *   - The trade sink: a buffer of ME_capacity() + 1 trades, reset per call.
 */
#include "engine_db.h"
#include "engine_db_adapter.h"
#include "../include/matching_engine_gen.h"

#include <stdlib.h>

static uint64_t g_cap;

typedef struct { uint64_t maker, taker, price, qty; } AdapterTrade;
static AdapterTrade *g_trades;
static uint64_t g_ntrades;

static struct Order *O(ME_OrderH h) { return (struct Order *)(void *)h; }
static struct PriceLevel *L(ME_LevelH h) { return (struct PriceLevel *)(void *)h; }
static ME_OrderH HO(struct Order *o) { return (ME_OrderH)(void *)o; }
static ME_LevelH HL(struct PriceLevel *l) { return (ME_LevelH)(void *)l; }

void ME_adapter_init(uint64_t capacity) {
    EngineDb_Init();
    g_cap = capacity;
    if (g_EngineDb.order_pool_total_allocated < capacity &&
        EngineDb_order_pool_ReserveMem(capacity - g_EngineDb.order_pool_total_allocated) == 0) abort();
    if (g_EngineDb.level_pool_total_allocated < capacity &&
        EngineDb_level_pool_ReserveMem(capacity - g_EngineDb.level_pool_total_allocated) == 0) abort();
    free(g_trades);
    g_trades = (AdapterTrade *)calloc(capacity + 1, sizeof(AdapterTrade));
    if (!g_trades) abort();
    g_ntrades = 0;
}

uint64_t ME_adapter_trade_count(void) { return g_ntrades; }
void ME_adapter_trade_get(uint64_t i, uint64_t *maker, uint64_t *taker,
                          uint64_t *price, uint64_t *qty) {
    *maker = g_trades[i].maker; *taker = g_trades[i].taker;
    *price = g_trades[i].price; *qty = g_trades[i].qty;
}

uint64_t ME_capacity(void) { return g_cap; }
uint64_t ME_order_count(void) { return g_EngineDb.order_pool_n; }

void ME_trade_reset(void) { g_ntrades = 0; }
void ME_trade_emit(uint64_t maker_id, uint64_t taker_id, uint64_t price, uint64_t qty) {
    if (g_ntrades > g_cap) abort();
    g_trades[g_ntrades].maker = maker_id; g_trades[g_ntrades].taker = taker_id;
    g_trades[g_ntrades].price = price; g_trades[g_ntrades].qty = qty;
    g_ntrades++;
}

ME_OrderH ME_order_alloc(void) {
    if (g_EngineDb.order_pool_n >= g_cap) return NULL;
    return HO(EngineDb_order_pool_Alloc());
}
void ME_order_free(ME_OrderH o) { EngineDb_order_pool_Free(O(o)); }
ME_LevelH ME_level_alloc(void) {
    if (g_EngineDb.level_pool_n >= g_cap) return NULL;
    return HL(EngineDb_level_pool_Alloc());
}
void ME_level_free(ME_LevelH l) { EngineDb_level_pool_Free(L(l)); }

uint64_t ME_order_get_id(ME_OrderH o) { return O(o)->id; }
uint64_t ME_order_get_account(ME_OrderH o) { return O(o)->account_id; }
uint64_t ME_order_get_side(ME_OrderH o) { return O(o)->side; }
uint64_t ME_order_get_stp_mode(ME_OrderH o) { return O(o)->stp_mode; }
uint64_t ME_order_get_price(ME_OrderH o) { return O(o)->price; }
uint64_t ME_order_get_qty(ME_OrderH o) { return O(o)->qty; }
uint64_t ME_order_get_remaining(ME_OrderH o) { return O(o)->remaining_qty; }
void ME_order_set_id(ME_OrderH o, uint64_t v) { O(o)->id = v; }
void ME_order_set_account(ME_OrderH o, uint64_t v) { O(o)->account_id = v; }
void ME_order_set_side(ME_OrderH o, uint64_t v) { O(o)->side = v; }
void ME_order_set_stp_mode(ME_OrderH o, uint64_t v) { O(o)->stp_mode = v; }
void ME_order_set_price(ME_OrderH o, uint64_t v) { O(o)->price = v; }
void ME_order_set_qty(ME_OrderH o, uint64_t v) { O(o)->qty = v; }
void ME_order_set_remaining(ME_OrderH h, uint64_t v) {
    struct Order *o = O(h);
    if (o->orders_inlist && o->p_price_level) {
        struct PriceLevel *l = o->p_price_level;
        l->total_qty = (l->total_qty - o->remaining_qty) + v;
    }
    o->remaining_qty = v;
}

uint64_t ME_level_get_price(ME_LevelH l) { return L(l)->price; }
uint64_t ME_level_get_count(ME_LevelH l) { return L(l)->orders_n; }
void ME_level_set_price(ME_LevelH l, uint64_t v) { L(l)->price = v; }

ME_OrderH ME_hash_find(uint64_t id) { return HO(EngineDb_ind_order_Find(id)); }
bool ME_hash_insert(ME_OrderH o) { return EngineDb_ind_order_InsertMaybe(O(o)); }
void ME_hash_remove(ME_OrderH o) { EngineDb_ind_order_Remove(O(o)); }

void ME_queue_insert_tail(ME_LevelH l, ME_OrderH o) { PriceLevel_orders_InsertTail(L(l), O(o)); }
void ME_queue_remove(ME_LevelH l, ME_OrderH o) { PriceLevel_orders_Remove(L(l), O(o)); }
ME_OrderH ME_queue_first(ME_LevelH l) { return HO(PriceLevel_orders_First(L(l))); }
ME_OrderH ME_queue_next(ME_OrderH o) { return HO(PriceLevel_orders_Next(O(o))); }
ME_LevelH ME_order_owner(ME_OrderH o) {
    return O(o)->orders_inlist ? HL(O(o)->p_price_level) : NULL;
}

ME_LevelH ME_bids_find(uint64_t price) { return HL(EngineDb_bids_Find(price)); }
void ME_bids_insert(ME_LevelH l) { EngineDb_bids_Insert(L(l)); }
void ME_bids_remove(ME_LevelH l) { EngineDb_bids_Remove(L(l)); }
ME_LevelH ME_bids_best(void) { return HL(EngineDb_bids_Best()); }
ME_LevelH ME_asks_find(uint64_t price) { return HL(EngineDb_asks_Find(price)); }
void ME_asks_insert(ME_LevelH l) { EngineDb_asks_Insert(L(l)); }
void ME_asks_remove(ME_LevelH l) { EngineDb_asks_Remove(L(l)); }
ME_LevelH ME_asks_best(void) { return HL(EngineDb_asks_Best()); }
