#pragma once
#include "matching_engine_gen.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef enum {
    SIDE_BUY  = 0,
    SIDE_SELL = 1
} OrderSide;

typedef enum {
    TYPE_LIMIT     = 0,
    TYPE_MARKET    = 1,
    TYPE_IOC       = 2,
    TYPE_POST_ONLY = 3
} OrderType;

typedef enum {
    STP_NONE                   = 0,
    STP_CANCEL_NEW             = 1,
    STP_CANCEL_OLD             = 2,
    STP_CANCEL_BOTH            = 3,
    STP_DECREMENT_AND_CONTINUE = 4
} StpMode;

typedef struct OrderRequest {
    uint64_t  id;
    uint64_t  account_id;
    uint8_t   side;       // 0 = Buy, 1 = Sell
    uint8_t   order_type; // Limit, Market, IOC, PostOnly
    uint8_t   stp_mode;   // STP policy
    uint64_t  price;
    uint64_t  qty;
} OrderRequest;

typedef struct TradeEvent {
    uint64_t aggressor_id;
    uint64_t passive_id;
    uint64_t price;
    uint64_t qty;
} TradeEvent;

typedef void (*TradeCallback)(const TradeEvent *trade, void *user_data);

typedef struct MatchingEngine {
    uint64_t total_trades;
    uint64_t total_volume;
    TradeCallback on_trade;
    void *user_data;
} MatchingEngine;

void MatchingEngine_Init(MatchingEngine *engine, TradeCallback cb, void *user_data);
bool MatchingEngine_ProcessOrder(MatchingEngine *engine, const OrderRequest *req);
bool MatchingEngine_CancelOrder(MatchingEngine *engine, uint64_t order_id);

// Invariant verification helpers (runtime assertions)
bool MatchingEngine_CheckInvariants(const MatchingEngine *engine);

#ifdef __cplusplus
}
#endif
