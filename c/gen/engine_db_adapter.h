/*
 * engine_db_adapter.h — set-up and trade access for the adapter that
 * implements engine_db.h on the handwritten data layer (c/src/matching_engine_gen.c).
 */
#ifndef ENGINE_DB_ADAPTER_H
#define ENGINE_DB_ADAPTER_H

#include <stdint.h>

/* (Re)initialise the data layer with the given pool capacity; clears it. */
void ME_adapter_init(uint64_t capacity);

/* Trades reported by the last matcher call (maker = passive, taker = aggressor). */
uint64_t ME_adapter_trade_count(void);
void ME_adapter_trade_get(uint64_t i, uint64_t *maker, uint64_t *taker,
                          uint64_t *price, uint64_t *qty);

#endif /* ENGINE_DB_ADAPTER_H */
