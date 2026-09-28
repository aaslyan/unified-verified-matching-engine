/*
 * total_overflow.c — the handwritten engine's latent level-total overflow
 * (docs/plan-v2/EVIDENCE.md §2). Without the v2 quantity bound (Qmax), two
 * resting orders of 2^63 at one price make the uint64_t level total wrap to 0;
 * MatchingEngine_CheckInvariants still passes, since its own sum wraps too.
 * The generated matcher rejects both orders: 2^63 exceeds Qmax for any capacity >= 1.
 * Prints the wrapped total; exits 0 when the wrap reproduces.
 */
#include "matching_engine.h"
#include "matching_engine_gen.h"

#include <inttypes.h>
#include <stdio.h>

int main(void) {
    MatchingEngine e;
    MatchingEngine_Init(&e, NULL, NULL);
    OrderRequest a = {1, 0, 0, 0, 0, 100, UINT64_C(1) << 63};
    OrderRequest b = {2, 0, 0, 0, 0, 100, UINT64_C(1) << 63};
    int ok = MatchingEngine_ProcessOrder(&e, &a) && MatchingEngine_ProcessOrder(&e, &b);
    uint64_t total = g_EngineDb.bids_root ? g_EngineDb.bids_root->total_qty : 1;
    printf("handwritten engine: both 2^63 orders accepted: %d; level total_qty = %" PRIu64
           " (true sum 2^64); CheckInvariants: %d\n", ok, total, MatchingEngine_CheckInvariants(&e));
    return (ok && total == 0) ? 0 : 1;
}
