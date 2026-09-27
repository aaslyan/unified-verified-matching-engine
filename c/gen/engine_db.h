/*
 * engine_db.h — the C face of the EngineDb contract (lean/Bridge/EngineDbApi.lean).
 *
 * The generated matcher (printed from lean/Matcher) calls only the functions
 * declared here. Any data layer that implements them and satisfies the
 * contract's laws can be linked underneath: plan v2 §3 trusts exactly that,
 * and Phase 5 tests it.
 *
 * Handles are opaque. NULL is "no handle": returned by a failed allocation
 * (pool full), a failed lookup, or the end of a queue. Passing NULL, or a
 * handle whose row was freed, to any function below is a contract violation;
 * the matcher is proved never to do it.
 *
 * Every numeric value is uint64_t, including the enumerations side and
 * stp_mode (whose values are small codes). A data layer that stores a
 * narrower field widens it; the matcher never does arithmetic on codes.
 *
 * Level totals are not part of the contract: a data layer that keeps them
 * maintains them itself, including when ME_order_set_remaining changes an
 * order's remaining quantity.
 */
#ifndef ENGINE_DB_H
#define ENGINE_DB_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct ME_OrderRec *ME_OrderH;
typedef struct ME_LevelRec *ME_LevelH;

/* Pool capacity (the same value bounds both pools) and live order count.
   Loop bounds and the trade-buffer bound in the matcher are computed from
   ME_capacity(), the same quantity the Lean semantics uses. */
uint64_t ME_capacity(void);
uint64_t ME_order_count(void);

/* Trade sink: the matcher reports each trade here, at most ME_capacity() + 1
   per call, after ME_trade_reset() at the start of each call. */
void ME_trade_reset(void);
void ME_trade_emit(uint64_t maker_id, uint64_t taker_id, uint64_t price, uint64_t qty);

/* Pools: NULL exactly when the pool is at capacity; the store is then unchanged. */
ME_OrderH ME_order_alloc(void);
void      ME_order_free(ME_OrderH o);   /* o must be in no queue and not hashed */
ME_LevelH ME_level_alloc(void);
void      ME_level_free(ME_LevelH l);   /* l must be in no tree, with an empty queue */

/* Order payload. */
uint64_t ME_order_get_id(ME_OrderH o);
uint64_t ME_order_get_account(ME_OrderH o);
uint64_t ME_order_get_side(ME_OrderH o);
uint64_t ME_order_get_stp_mode(ME_OrderH o);
uint64_t ME_order_get_price(ME_OrderH o);
uint64_t ME_order_get_qty(ME_OrderH o);
uint64_t ME_order_get_remaining(ME_OrderH o);
void ME_order_set_id(ME_OrderH o, uint64_t v);        /* only while not hashed */
void ME_order_set_account(ME_OrderH o, uint64_t v);
void ME_order_set_side(ME_OrderH o, uint64_t v);
void ME_order_set_stp_mode(ME_OrderH o, uint64_t v);
void ME_order_set_price(ME_OrderH o, uint64_t v);
void ME_order_set_qty(ME_OrderH o, uint64_t v);
void ME_order_set_remaining(ME_OrderH o, uint64_t v);

/* Level fields. count is the queue length (orders_n), read-only. */
uint64_t ME_level_get_price(ME_LevelH l);
uint64_t ME_level_get_count(ME_LevelH l);
void ME_level_set_price(ME_LevelH l, uint64_t v);     /* only while in no tree */

/* Order-id hash index. */
ME_OrderH ME_hash_find(uint64_t id);
bool      ME_hash_insert(ME_OrderH o);  /* false (unchanged) if the id is present */
void      ME_hash_remove(ME_OrderH o);  /* o must be hashed */

/* FIFO queue per level. */
void      ME_queue_insert_tail(ME_LevelH l, ME_OrderH o);  /* o in no queue */
void      ME_queue_remove(ME_LevelH l, ME_OrderH o);       /* o in l's queue */
ME_OrderH ME_queue_first(ME_LevelH l);
ME_OrderH ME_queue_next(ME_OrderH o);                      /* o in some queue */
ME_LevelH ME_order_owner(ME_OrderH o);                     /* NULL if in no queue */

/* Price trees: bids (best = highest), asks (best = lowest). */
ME_LevelH ME_bids_find(uint64_t price);
void      ME_bids_insert(ME_LevelH l);  /* l in no tree, price not in bids */
void      ME_bids_remove(ME_LevelH l);  /* l in bids */
ME_LevelH ME_bids_best(void);
ME_LevelH ME_asks_find(uint64_t price);
void      ME_asks_insert(ME_LevelH l);
void      ME_asks_remove(ME_LevelH l);
ME_LevelH ME_asks_best(void);

#endif /* ENGINE_DB_H */
