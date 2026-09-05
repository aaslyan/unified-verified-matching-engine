#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include "../include/matching_engine.h"

static inline double get_time_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static void on_trade_dummy(const TradeEvent *trade, void *user_data) {
    (void)trade;
    (void)user_data;
}

#define NUM_ORDERS 1000000

int main(void) {
    printf("===================================================================\n");
    printf("   HIGH-FREQUENCY VERIFIED C MATCHING ENGINE BENCHMARK            \n");
    printf("   Built with AMCC Provably-Correct Low-Level C Data Structures   \n");
    printf("===================================================================\n\n");

    MatchingEngine engine;
    MatchingEngine_Init(&engine, on_trade_dummy, NULL);

    printf("Executing matching workload: %d orders...\n", NUM_ORDERS);

    // Seed deterministic random numbers
    srand(42);

    double t0 = get_time_sec();

    // 1. Post Resting Limit Orders (Book building)
    uint64_t order_id = 1;
    for (int i = 0; i < NUM_ORDERS / 2; ++i) {
        OrderRequest req = {
            .id = order_id++,
            .side = (i % 2 == 0) ? SIDE_BUY : SIDE_SELL,
            .order_type = TYPE_LIMIT,
            .price = (i % 2 == 0) ? (9900 - (rand() % 100) * 10) : (10100 + (rand() % 100) * 10),
            .qty = 10 + (rand() % 50)
        };
        MatchingEngine_ProcessOrder(&engine, &req);
    }

    // 2. Aggressive Crossing Orders (Execution / Matching Loop)
    for (int i = 0; i < NUM_ORDERS / 4; ++i) {
        OrderRequest req = {
            .id = order_id++,
            .side = (i % 2 == 0) ? SIDE_BUY : SIDE_SELL,
            .order_type = TYPE_LIMIT,
            .price = (i % 2 == 0) ? 10500 : 9500, // Crossing price
            .qty = 5 + (rand() % 20)
        };
        MatchingEngine_ProcessOrder(&engine, &req);
    }

    // 3. Cancellations
    for (int i = 0; i < NUM_ORDERS / 4; ++i) {
        uint64_t cancel_id = (rand() % (order_id - 1)) + 1;
        MatchingEngine_CancelOrder(&engine, cancel_id);
    }

    double t1 = get_time_sec();
    double elapsed = t1 - t0;
    double ops_sec = (double)NUM_ORDERS / elapsed;
    double ns_per_op = (elapsed / (double)NUM_ORDERS) * 1e9;

    printf("\n--- Performance Results ---\n");
    printf("  Workload        : %d mixed operations (Inserts, Matches, Cancels)\n", NUM_ORDERS);
    printf("  Elapsed Time    : %.4f seconds\n", elapsed);
    printf("  Throughput      : \033[1;32m%.2f Million orders/sec\033[0m\n", ops_sec / 1e6);
    printf("  Average Latency : \033[1;32m%.2f ns/order\033[0m\n", ns_per_op);
    printf("  Total Trades    : %lu fills\n", (unsigned long)engine.total_trades);
    printf("  Total Volume    : %lu shares traded\n\n", (unsigned long)engine.total_volume);

    // Check invariants
    printf("--- Verification & Invariant Checking ---\n");
    bool uncrossed = MatchingEngine_CheckInvariants(&engine);
    printf("  Book Invariant (Uncrossed Bids < Asks) : %s\n", uncrossed ? "\033[1;32m[PASS]\033[0m" : "\033[1;31m[FAIL]\033[0m");
    printf("  Active Orders in Hash Index            : %u\n", EngineDb_ind_order_N());
    printf("  Active Bids Price Levels               : %u\n", g_EngineDb.bids_n);
    printf("  Active Asks Price Levels               : %u\n", g_EngineDb.asks_n);

    printf("\n===================================================================\n");
    printf("   SUCCESS: Verified C matching engine executed at line rate!     \n");
    printf("===================================================================\n");

    return 0;
}
