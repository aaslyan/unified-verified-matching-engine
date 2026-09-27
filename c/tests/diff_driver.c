/*
 * diff_driver.c — prints a trace of a seeded random request stream: the
 * return value of each call, its trades, the book after it, and the invariant
 * check. Built once against the handwritten engine and once against the
 * generated matcher (scripts/matcher_c_diff.sh); the two traces must be equal.
 */
#include "../include/matching_engine.h"
#include "../include/matching_engine_gen.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t rng;
static uint64_t next_rand(void) {
    rng = rng * UINT64_C(6364136223846793005) + UINT64_C(1442695040888963407);
    return rng >> 33;
}
static uint64_t pick(uint64_t n) { return next_rand() % n; }

static void on_trade(const TradeEvent *t, void *ud) {
    (void)ud;
    printf("  trade taker=%" PRIu64 " maker=%" PRIu64 " px=%" PRIu64 " qty=%" PRIu64 "\n",
           t->aggressor_id, t->passive_id, t->price, t->qty);
}

static void dump_level(const struct PriceLevel *l) {
    printf("   %" PRIu64 " (n=%" PRIu32 " tot=%" PRIu64 "):", l->price, l->orders_n, l->total_qty);
    for (const struct Order *o = l->orders_head; o; o = o->orders_next)
        printf(" %" PRIu64 "/%" PRIu64, o->id, o->remaining_qty);
    printf("\n");
}
static void dump_tree(const struct PriceLevel *n) {
    if (!n) return;
    dump_tree(n->tree_left);
    dump_level(n);
    dump_tree(n->tree_right);
}

int main(int argc, char **argv) {
    uint64_t seed = argc > 1 ? strtoull(argv[1], 0, 10) : 1;
    uint64_t steps = argc > 2 ? strtoull(argv[2], 0, 10) : 1000;
    rng = seed;
    MatchingEngine e;
    MatchingEngine_Init(&e, on_trade, NULL);
    uint64_t next_id = 1;
    for (uint64_t i = 0; i < steps; ++i) {
        uint64_t id = next_id;
        if (pick(10) < 2 && next_id > 1) id = 1 + pick(next_id - 1); else next_id++;
        if (pick(10) < 2) {
            bool ok = MatchingEngine_CancelOrder(&e, id);
            printf("%" PRIu64 " cancel %" PRIu64 " -> %d\n", i, id, ok);
        } else {
            uint64_t tr = pick(20);
            OrderRequest r;
            r.id = id;
            r.account_id = pick(3);
            r.side = (uint8_t)pick(2);
            r.order_type = (uint8_t)(tr < 9 ? 0 : tr < 12 ? 1 : tr < 15 ? 2 : tr < 19 ? 3 : 5);
            uint64_t sr = pick(12);
            r.stp_mode = (uint8_t)(sr < 6 ? 0 : sr < 11 ? 1 + pick(4) : 7);
            r.price = pick(30) == 0 ? 0 : 95 + pick(11);
            r.qty = pick(40) == 0 ? 0 : 1 + pick(9);
            bool ok = MatchingEngine_ProcessOrder(&e, &r);
            printf("%" PRIu64 " order id=%" PRIu64 " acct=%" PRIu64 " side=%u type=%u stp=%u px=%" PRIu64
                   " qty=%" PRIu64 " -> %d\n", i, r.id, r.account_id, r.side, r.order_type, r.stp_mode,
                   r.price, r.qty, ok);
        }
        printf("  bids:\n"); dump_tree(g_EngineDb.bids_root);
        printf("  asks:\n"); dump_tree(g_EngineDb.asks_root);
        printf("  inv=%d\n", MatchingEngine_CheckInvariants(&e));
    }
    return 0;
}
