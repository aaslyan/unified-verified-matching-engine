/*
 * runner.c — runs a request stream (tests/differential/gen_stream.py format)
 * through a C engine and prints, after each request, the observation in the
 * format of the Lean oracle (lean/Matcher/Oracle.lean):
 *
 *   <step> code <k>                (GEN: the generated matcher's result code)
 *   <step> ok <0|1>                (HW:  the handwritten engine's bool result)
 *     trade <maker> <taker> <price> <qty>
 *     bid <price> : <id>/<remaining>/<qty>/<account>/<policy> ...   (best first)
 *     ask <price> : ...
 *
 * Built with -DRUN_GEN against the generated matcher (c/gen/matcher.c) +
 * adapter + handwritten data layer, or with -DRUN_HW against the handwritten
 * engine (c/src/matching_engine.c) + the same data layer.
 */
#include "../../c/include/matching_engine.h"
#include "../../c/include/matching_engine_gen.h"
#ifdef RUN_GEN
#include "engine_db_adapter.h"
uint64_t gen_process_order(uint64_t id, uint64_t account, uint64_t side, uint64_t otype,
                           uint64_t stp, uint64_t price, uint64_t qty);
uint64_t gen_cancel_order(uint64_t id);
#endif

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void dump_level(const char *tag, const struct PriceLevel *l) {
    printf("  %s %" PRIu64 " :", tag, l->price);
    for (const struct Order *o = l->orders_head; o; o = o->orders_next)
        printf(" %" PRIu64 "/%" PRIu64 "/%" PRIu64 "/%" PRIu64 "/%" PRIu64, o->id, o->remaining_qty,
               o->qty, o->account_id, o->account_id == 0 ? UINT64_C(0) : o->stp_mode);
    printf("\n");
}
/* bids: highest first (reverse in-order); asks: lowest first (in-order). */
static void dump_bids(const struct PriceLevel *n) {
    if (!n) return;
    dump_bids(n->tree_right); dump_level("bid", n); dump_bids(n->tree_left);
}
static void dump_asks(const struct PriceLevel *n) {
    if (!n) return;
    dump_asks(n->tree_left); dump_level("ask", n); dump_asks(n->tree_right);
}

#ifdef RUN_HW
/* Trades arrive during the call; they are printed after the step's head line. */
static TradeEvent g_tr[4096];
static uint64_t g_ntr;
static void on_trade(const TradeEvent *t, void *ud) {
    (void)ud;
    if (g_ntr < 4096) g_tr[g_ntr] = *t;
    g_ntr++;
}
static void flush_trades(void) {
    for (uint64_t i = 0; i < g_ntr && i < 4096; ++i)
        printf("  trade %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n", g_tr[i].passive_id,
               g_tr[i].aggressor_id, g_tr[i].price, g_tr[i].qty);
    g_ntr = 0;
}
#endif

int main(int argc, char **argv) {
    uint64_t cap = argc > 1 ? strtoull(argv[1], 0, 10) : 8;
    FILE *in = argc > 2 ? fopen(argv[2], "r") : stdin;
    if (!in) return 2;
#ifdef RUN_GEN
    ME_adapter_init(cap);
#else
    (void)cap;
    MatchingEngine e;
    MatchingEngine_Init(&e, on_trade, NULL);
#endif
    char line[256];
    uint64_t k = 0;
    while (fgets(line, sizeof line, in)) {
        uint64_t id, acct, side, type, stp, price, qty;
        if (sscanf(line, "O %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64,
                   &id, &acct, &side, &type, &stp, &price, &qty) == 7) {
#ifdef RUN_GEN
            uint64_t c = gen_process_order(id, acct, side, type, stp, price, qty);
            printf("%" PRIu64 " code %" PRIu64 "\n", k, c);
#else
            OrderRequest r = { id, acct, (uint8_t)side, (uint8_t)type, (uint8_t)stp, price, qty };
            int ok = (int)MatchingEngine_ProcessOrder(&e, &r);
            printf("%" PRIu64 " ok %d\n", k, ok);
#endif
        } else if (sscanf(line, "C %" SCNu64, &id) == 1) {
#ifdef RUN_GEN
            uint64_t c = gen_cancel_order(id);
            printf("%" PRIu64 " code %" PRIu64 "\n", k, c);
#else
            printf("%" PRIu64 " ok %d\n", k, (int)MatchingEngine_CancelOrder(&e, id));
#endif
        } else continue;
#ifdef RUN_HW
        flush_trades();
#endif
#ifdef RUN_GEN
        for (uint64_t i = 0; i < ME_adapter_trade_count(); ++i) {
            uint64_t m, t, p, q;
            ME_adapter_trade_get(i, &m, &t, &p, &q);
            printf("  trade %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n", m, t, p, q);
        }
#endif
        dump_bids(g_EngineDb.bids_root);
        dump_asks(g_EngineDb.asks_root);
        k++;
    }
    return 0;
}
