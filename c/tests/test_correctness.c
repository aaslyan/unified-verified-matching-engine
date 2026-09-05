#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include "../include/matching_engine.h"

static void dummy_trade_cb(const TradeEvent *trade, void *user_data) {
    (void)trade;
    (void)user_data;
}

static void test_duplicate_order_id_rejection(void) {
    printf("[TEST] Running duplicate order ID rejection test...\n");
    MatchingEngine engine;
    MatchingEngine_Init(&engine, dummy_trade_cb, NULL);

    OrderRequest o1 = { .id = 1001, .side = SIDE_BUY, .order_type = TYPE_LIMIT, .price = 100, .qty = 10 };
    bool ok1 = MatchingEngine_ProcessOrder(&engine, &o1);
    assert(ok1 == true);
    assert(MatchingEngine_CheckInvariants(&engine) == true);
    assert(EngineDb_ind_order_N() == 1);

    // Duplicate order with same ID must be rejected!
    OrderRequest o2 = { .id = 1001, .side = SIDE_BUY, .order_type = TYPE_LIMIT, .price = 105, .qty = 20 };
    bool ok2 = MatchingEngine_ProcessOrder(&engine, &o2);
    assert(ok2 == false);
    assert(MatchingEngine_CheckInvariants(&engine) == true);
    assert(EngineDb_ind_order_N() == 1);

    // Duplicate order on opposing side must also be rejected!
    OrderRequest o3 = { .id = 1001, .side = SIDE_SELL, .order_type = TYPE_LIMIT, .price = 110, .qty = 5 };
    bool ok3 = MatchingEngine_ProcessOrder(&engine, &o3);
    assert(ok3 == false);
    assert(MatchingEngine_CheckInvariants(&engine) == true);
    assert(EngineDb_ind_order_N() == 1);

    // Cancel order 1001
    bool ok_cancel = MatchingEngine_CancelOrder(&engine, 1001);
    assert(ok_cancel == true);
    assert(MatchingEngine_CheckInvariants(&engine) == true);
    assert(EngineDb_ind_order_N() == 0);

    // After cancellation, order 1001 ID can be reused safely
    OrderRequest o4 = { .id = 1001, .side = SIDE_SELL, .order_type = TYPE_LIMIT, .price = 120, .qty = 15 };
    bool ok4 = MatchingEngine_ProcessOrder(&engine, &o4);
    assert(ok4 == true);
    assert(MatchingEngine_CheckInvariants(&engine) == true);
    assert(EngineDb_ind_order_N() == 1);

    EngineDb_Destroy();
    printf("  -> PASSED\n");
}

static void test_matching_and_fifo(void) {
    printf("[TEST] Running matching and FIFO queue execution test...\n");
    MatchingEngine engine;
    MatchingEngine_Init(&engine, dummy_trade_cb, NULL);

    // Post resting asks: 3 orders at price 200
    OrderRequest a1 = { .id = 1, .side = SIDE_SELL, .order_type = TYPE_LIMIT, .price = 200, .qty = 10 };
    OrderRequest a2 = { .id = 2, .side = SIDE_SELL, .order_type = TYPE_LIMIT, .price = 200, .qty = 20 };
    OrderRequest a3 = { .id = 3, .side = SIDE_SELL, .order_type = TYPE_LIMIT, .price = 200, .qty = 30 };
    assert(MatchingEngine_ProcessOrder(&engine, &a1));
    assert(MatchingEngine_ProcessOrder(&engine, &a2));
    assert(MatchingEngine_ProcessOrder(&engine, &a3));
    assert(MatchingEngine_CheckInvariants(&engine));
    assert(g_EngineDb.asks_n == 1);
    assert(EngineDb_ind_order_N() == 3);

    // Aggressive buy order of 25 shares at 200
    // Fills a1 (10 shares), partially fills a2 (15 shares), leaves a2 with 5 shares, a3 untouched with 30
    OrderRequest b1 = { .id = 4, .side = SIDE_BUY, .order_type = TYPE_LIMIT, .price = 200, .qty = 25 };
    assert(MatchingEngine_ProcessOrder(&engine, &b1));
    assert(MatchingEngine_CheckInvariants(&engine));
    assert(engine.total_trades == 2);
    assert(engine.total_volume == 25);
    assert(EngineDb_ind_order_N() == 2); // a1 is gone, a2 and a3 remain
    assert(EngineDb_ind_order_Find(1) == NULL);
    assert(EngineDb_ind_order_Find(2) != NULL);
    assert(EngineDb_ind_order_Find(3) != NULL);

    // Check remaining quantities
    struct Order *rem_a2 = EngineDb_ind_order_Find(2);
    assert(rem_a2->remaining_qty == 5);
    struct Order *rem_a3 = EngineDb_ind_order_Find(3);
    assert(rem_a3->remaining_qty == 30);

    // Sweep remaining asks (35 shares)
    OrderRequest b2 = { .id = 5, .side = SIDE_BUY, .order_type = TYPE_MARKET, .price = 0, .qty = 35 };
    assert(MatchingEngine_ProcessOrder(&engine, &b2));
    assert(MatchingEngine_CheckInvariants(&engine));
    assert(g_EngineDb.asks_n == 0);
    assert(EngineDb_ind_order_N() == 0);
    assert(engine.total_trades == 4);
    assert(engine.total_volume == 60);

    EngineDb_Destroy();
    printf("  -> PASSED\n");
}

static void test_post_only_and_uncrossed(void) {
    printf("[TEST] Running post-only and uncrossed invariants test...\n");
    MatchingEngine engine;
    MatchingEngine_Init(&engine, dummy_trade_cb, NULL);

    OrderRequest a1 = { .id = 10, .side = SIDE_SELL, .order_type = TYPE_LIMIT, .price = 150, .qty = 10 };
    assert(MatchingEngine_ProcessOrder(&engine, &a1));

    // Post-only buy at price 155 crosses resting ask at 150 -> MUST BE REJECTED
    OrderRequest po1 = { .id = 11, .side = SIDE_BUY, .order_type = TYPE_POST_ONLY, .price = 155, .qty = 5 };
    assert(MatchingEngine_ProcessOrder(&engine, &po1) == false);
    assert(MatchingEngine_CheckInvariants(&engine));
    assert(EngineDb_ind_order_Find(11) == NULL);

    // Post-only buy at price 145 does not cross -> ACCEPTED
    OrderRequest po2 = { .id = 12, .side = SIDE_BUY, .order_type = TYPE_POST_ONLY, .price = 145, .qty = 5 };
    assert(MatchingEngine_ProcessOrder(&engine, &po2) == true);
    assert(MatchingEngine_CheckInvariants(&engine));

    // Post-only sell at price 140 crosses resting bid at 145 -> MUST BE REJECTED
    OrderRequest po3 = { .id = 13, .side = SIDE_SELL, .order_type = TYPE_POST_ONLY, .price = 140, .qty = 5 };
    assert(MatchingEngine_ProcessOrder(&engine, &po3) == false);
    assert(MatchingEngine_CheckInvariants(&engine));

    EngineDb_Destroy();
    printf("  -> PASSED\n");
}

int main(void) {
    printf("===================================================================\n");
    printf("   RUNNING MATCHING ENGINE CORRECTNESS & INVARIANT TEST SUITE     \n");
    printf("===================================================================\n");

    test_duplicate_order_id_rejection();
    test_matching_and_fifo();
    test_post_only_and_uncrossed();

    printf("\n===================================================================\n");
    printf("   ALL CORRECTNESS AND INVARIANT TESTS PASSED (100%% OK)           \n");
    printf("===================================================================\n");
    return 0;
}
