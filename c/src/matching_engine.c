#include "../include/matching_engine.h"
#include <stdio.h>
#include <string.h>

void MatchingEngine_Init(MatchingEngine *engine, TradeCallback cb, void *user_data) {
    EngineDb_Init();
    if (engine) {
        engine->total_trades = 0;
        engine->total_volume = 0;
        engine->on_trade = cb;
        engine->user_data = user_data;
    }
}

static inline uint64_t min_u64(uint64_t a, uint64_t b) {
    return a < b ? a : b;
}

bool MatchingEngine_ProcessOrder(MatchingEngine *engine, const OrderRequest *req) {
    if (!req || req->qty == 0) return false;
    if (req->order_type == TYPE_LIMIT && req->price == 0) return false;

    // Reject duplicate order IDs upfront before modifying any book state
    if (EngineDb_ind_order_Find(req->id) != NULL) {
        return false;
    }

    uint64_t rem_qty = req->qty;

    if (req->side == SIDE_BUY) {
        // PostOnly check: cannot cross resting ask
        if (req->order_type == TYPE_POST_ONLY) {
            struct PriceLevel *best_ask = EngineDb_asks_Best();
            if (best_ask != NULL && best_ask->price <= req->price) {
                return false; // Reject post-only crossed order
            }
        }

        // Match against Asks (Lowest Price First)
        while (rem_qty > 0) {
            struct PriceLevel *best_ask = EngineDb_asks_Best();
            if (best_ask == NULL) break;
            if (req->order_type != TYPE_MARKET && best_ask->price > req->price) break;

            struct Order *passive = PriceLevel_orders_First(best_ask);
            while (passive != NULL && rem_qty > 0) {
                // Self-Trade Prevention Check
                if (req->account_id != 0 && req->account_id == passive->account_id) {
                    if (req->stp_mode == STP_CANCEL_NEW) {
                        rem_qty = 0;
                        break;
                    } else if (req->stp_mode == STP_CANCEL_OLD || req->stp_mode == STP_CANCEL_BOTH) {
                        struct Order *to_cancel = passive;
                        passive = PriceLevel_orders_Next(passive);
                        best_ask->total_qty -= to_cancel->remaining_qty;
                        PriceLevel_orders_Remove(best_ask, to_cancel);
                        EngineDb_ind_order_Remove(to_cancel);
                        EngineDb_order_pool_Free(to_cancel);
                        if (req->stp_mode == STP_CANCEL_BOTH) {
                            rem_qty = 0;
                            break;
                        }
                        continue;
                    } else if (req->stp_mode == STP_DECREMENT_AND_CONTINUE) {
                        uint64_t decr = min_u64(rem_qty, passive->remaining_qty);
                        rem_qty -= decr;
                        passive->remaining_qty -= decr;
                        best_ask->total_qty -= decr;
                        struct Order *next_passive = PriceLevel_orders_Next(passive);
                        if (passive->remaining_qty == 0) {
                            PriceLevel_orders_Remove(best_ask, passive);
                            EngineDb_ind_order_Remove(passive);
                            EngineDb_order_pool_Free(passive);
                        }
                        passive = next_passive;
                        continue;
                    }
                }

                uint64_t fill_qty = min_u64(rem_qty, passive->remaining_qty);
                rem_qty -= fill_qty;
                passive->remaining_qty -= fill_qty;
                best_ask->total_qty -= fill_qty;

                if (engine) {
                    engine->total_trades++;
                    engine->total_volume += fill_qty;
                    if (engine->on_trade) {
                        TradeEvent trade = {
                            .aggressor_id = req->id,
                            .passive_id = passive->id,
                            .price = best_ask->price,
                            .qty = fill_qty
                        };
                        engine->on_trade(&trade, engine->user_data);
                    }
                }

                struct Order *next_passive = PriceLevel_orders_Next(passive);
                if (passive->remaining_qty == 0) {
                    PriceLevel_orders_Remove(best_ask, passive);
                    EngineDb_ind_order_Remove(passive);
                    EngineDb_order_pool_Free(passive);
                }
                passive = next_passive;
            }

            if (best_ask->orders_n == 0) {
                EngineDb_asks_Remove(best_ask);
                EngineDb_level_pool_Free(best_ask);
            }
        }

        // Post remaining to Bids book if limit order (and not IOC / Market)
        if (rem_qty > 0 && req->order_type != TYPE_IOC && req->order_type != TYPE_MARKET) {
            struct Order *ord = EngineDb_order_pool_Alloc();
            if (!ord) return false;

            ord->id = req->id;
            ord->account_id = req->account_id;
            ord->side = req->side;
            ord->stp_mode = req->stp_mode;
            ord->price = req->price;
            ord->qty = req->qty;
            ord->remaining_qty = rem_qty;

            struct PriceLevel *lvl = EngineDb_bids_Find(req->price);
            bool is_new_lvl = false;
            if (lvl == NULL) {
                lvl = EngineDb_level_pool_Alloc();
                if (!lvl) {
                    EngineDb_order_pool_Free(ord);
                    return false;
                }
                lvl->price = req->price;
                EngineDb_bids_Insert(lvl);
                is_new_lvl = true;
            }

            PriceLevel_orders_InsertTail(lvl, ord);
            if (!EngineDb_ind_order_InsertMaybe(ord)) {
                // Roll back in case of unexpected hash insertion collision
                PriceLevel_orders_Remove(lvl, ord);
                if (lvl->orders_n == 0 && is_new_lvl) {
                    EngineDb_bids_Remove(lvl);
                    EngineDb_level_pool_Free(lvl);
                }
                EngineDb_order_pool_Free(ord);
                return false;
            }
        }
    } else {
        // SIDE_SELL
        if (req->order_type == TYPE_POST_ONLY) {
            struct PriceLevel *best_bid = EngineDb_bids_Best();
            if (best_bid != NULL && best_bid->price >= req->price) {
                return false;
            }
        }

        // Match against Bids (Highest Price First)
        while (rem_qty > 0) {
            struct PriceLevel *best_bid = EngineDb_bids_Best();
            if (best_bid == NULL) break;
            if (req->order_type != TYPE_MARKET && best_bid->price < req->price) break;

            struct Order *passive = PriceLevel_orders_First(best_bid);
            while (passive != NULL && rem_qty > 0) {
                // Self-Trade Prevention Check
                if (req->account_id != 0 && req->account_id == passive->account_id) {
                    if (req->stp_mode == STP_CANCEL_NEW) {
                        rem_qty = 0;
                        break;
                    } else if (req->stp_mode == STP_CANCEL_OLD || req->stp_mode == STP_CANCEL_BOTH) {
                        struct Order *to_cancel = passive;
                        passive = PriceLevel_orders_Next(passive);
                        best_bid->total_qty -= to_cancel->remaining_qty;
                        PriceLevel_orders_Remove(best_bid, to_cancel);
                        EngineDb_ind_order_Remove(to_cancel);
                        EngineDb_order_pool_Free(to_cancel);
                        if (req->stp_mode == STP_CANCEL_BOTH) {
                            rem_qty = 0;
                            break;
                        }
                        continue;
                    } else if (req->stp_mode == STP_DECREMENT_AND_CONTINUE) {
                        uint64_t decr = min_u64(rem_qty, passive->remaining_qty);
                        rem_qty -= decr;
                        passive->remaining_qty -= decr;
                        best_bid->total_qty -= decr;
                        struct Order *next_passive = PriceLevel_orders_Next(passive);
                        if (passive->remaining_qty == 0) {
                            PriceLevel_orders_Remove(best_bid, passive);
                            EngineDb_ind_order_Remove(passive);
                            EngineDb_order_pool_Free(passive);
                        }
                        passive = next_passive;
                        continue;
                    }
                }

                uint64_t fill_qty = min_u64(rem_qty, passive->remaining_qty);
                rem_qty -= fill_qty;
                passive->remaining_qty -= fill_qty;
                best_bid->total_qty -= fill_qty;

                if (engine) {
                    engine->total_trades++;
                    engine->total_volume += fill_qty;
                    if (engine->on_trade) {
                        TradeEvent trade = {
                            .aggressor_id = req->id,
                            .passive_id = passive->id,
                            .price = best_bid->price,
                            .qty = fill_qty
                        };
                        engine->on_trade(&trade, engine->user_data);
                    }
                }

                struct Order *next_passive = PriceLevel_orders_Next(passive);
                if (passive->remaining_qty == 0) {
                    PriceLevel_orders_Remove(best_bid, passive);
                    EngineDb_ind_order_Remove(passive);
                    EngineDb_order_pool_Free(passive);
                }
                passive = next_passive;
            }

            if (best_bid->orders_n == 0) {
                EngineDb_bids_Remove(best_bid);
                EngineDb_level_pool_Free(best_bid);
            }
        }

        // Post remaining to Asks book if limit order
        if (rem_qty > 0 && req->order_type != TYPE_IOC && req->order_type != TYPE_MARKET) {
            struct Order *ord = EngineDb_order_pool_Alloc();
            if (!ord) return false;

            ord->id = req->id;
            ord->account_id = req->account_id;
            ord->side = req->side;
            ord->stp_mode = req->stp_mode;
            ord->price = req->price;
            ord->qty = req->qty;
            ord->remaining_qty = rem_qty;

            struct PriceLevel *lvl = EngineDb_asks_Find(req->price);
            bool is_new_lvl = false;
            if (lvl == NULL) {
                lvl = EngineDb_level_pool_Alloc();
                if (!lvl) {
                    EngineDb_order_pool_Free(ord);
                    return false;
                }
                lvl->price = req->price;
                EngineDb_asks_Insert(lvl);
                is_new_lvl = true;
            }

            PriceLevel_orders_InsertTail(lvl, ord);
            if (!EngineDb_ind_order_InsertMaybe(ord)) {
                // Roll back in case of unexpected hash insertion collision
                PriceLevel_orders_Remove(lvl, ord);
                if (lvl->orders_n == 0 && is_new_lvl) {
                    EngineDb_asks_Remove(lvl);
                    EngineDb_level_pool_Free(lvl);
                }
                EngineDb_order_pool_Free(ord);
                return false;
            }
        }
    }

    return true;
}

bool MatchingEngine_CancelOrder(MatchingEngine *engine, uint64_t order_id) {
    (void)engine;
    struct Order *ord = EngineDb_ind_order_Find(order_id);
    if (!ord || !ord->p_price_level) return false;

    struct PriceLevel *lvl = ord->p_price_level;
    PriceLevel_orders_Remove(lvl, ord);
    EngineDb_ind_order_Remove(ord);
    EngineDb_order_pool_Free(ord);

    if (lvl->orders_n == 0) {
        if (ord->side == SIDE_BUY) {
            EngineDb_bids_Remove(lvl);
        } else {
            EngineDb_asks_Remove(lvl);
        }
        EngineDb_level_pool_Free(lvl);
    }
    return true;
}

// -----------------------------------------------------------------------------
// Invariant Verification
// -----------------------------------------------------------------------------

static bool validate_price_level(const struct PriceLevel *lvl, uint8_t expected_side, uint32_t *order_count_acc) {
    if (!lvl) return false;
    if (lvl->orders_n == 0) return false; // No empty levels allowed in tree

    uint32_t count = 0;
    uint64_t sum_qty = 0;
    const struct Order *prev = NULL;

    for (const struct Order *ord = lvl->orders_head; ord != NULL; ord = ord->orders_next) {
        if (ord->orders_prev != prev) return false; // Inconsistent prev link
        if (ord->p_price_level != lvl) return false;
        if (ord->price != lvl->price) return false;
        if (ord->side != expected_side) return false;
        if (ord->remaining_qty == 0 || ord->remaining_qty > ord->qty) return false; // No ghost orders
        if (!ord->orders_inlist) return false;
        if (!ord->ind_order_inhash) return false;

        // Hash index agreement
        if (EngineDb_ind_order_Find(ord->id) != ord) return false;

        sum_qty += ord->remaining_qty;
        count++;
        prev = ord;
    }

    if (lvl->orders_tail != prev) return false; // Inconsistent tail link
    if (lvl->orders_n != count) return false;
    if (lvl->total_qty != sum_qty) return false;

    if (order_count_acc) {
        *order_count_acc += count;
    }
    return true;
}

static bool validate_bst(const struct PriceLevel *node, const struct PriceLevel *parent,
                         uint64_t min_price, uint64_t max_price,
                         bool has_min, bool has_max,
                         uint32_t *node_count_acc, uint8_t side, uint32_t *order_count_acc) {
    if (node == NULL) return true;

    if (node->tree_parent != parent) return false;
    if (!node->tree_intree) return false;

    if (has_min && node->price <= min_price) return false;
    if (has_max && node->price >= max_price) return false;

    if (!validate_price_level(node, side, order_count_acc)) return false;

    if (node_count_acc) (*node_count_acc)++;

    if (!validate_bst(node->tree_left, node, min_price, node->price, has_min, true, node_count_acc, side, order_count_acc)) {
        return false;
    }
    if (!validate_bst(node->tree_right, node, node->price, max_price, true, has_max, node_count_acc, side, order_count_acc)) {
        return false;
    }
    return true;
}

bool MatchingEngine_CheckInvariants(const MatchingEngine *engine) {
    (void)engine;

    // 1. Uncrossed Book
    struct PriceLevel *best_bid = EngineDb_bids_Best();
    struct PriceLevel *best_ask = EngineDb_asks_Best();
    if (best_bid != NULL && best_ask != NULL) {
        if (best_bid->price >= best_ask->price) {
            return false;
        }
    }

    // 2. BST Validity and Level Queue Validation
    uint32_t bids_node_count = 0;
    uint32_t bids_order_count = 0;
    if (!validate_bst(g_EngineDb.bids_root, NULL, 0, 0, false, false, &bids_node_count, SIDE_BUY, &bids_order_count)) {
        return false;
    }
    if (bids_node_count != g_EngineDb.bids_n) return false;

    uint32_t asks_node_count = 0;
    uint32_t asks_order_count = 0;
    if (!validate_bst(g_EngineDb.asks_root, NULL, 0, 0, false, false, &asks_node_count, SIDE_SELL, &asks_order_count)) {
        return false;
    }
    if (asks_node_count != g_EngineDb.asks_n) return false;

    // 3. Hash Index & Pool Agreement
    uint32_t total_resting_orders = bids_order_count + asks_order_count;
    if (g_EngineDb.ind_order_n != total_resting_orders) return false;
    if (g_EngineDb.order_pool_n != total_resting_orders) return false;
    if (g_EngineDb.level_pool_n != (g_EngineDb.bids_n + g_EngineDb.asks_n)) return false;

    // 4. Verify all hash table buckets
    if (g_EngineDb.ind_order_buckets) {
        uint32_t hash_entry_count = 0;
        for (uint32_t b = 0; b < ORDER_HASH_BUCKETS; ++b) {
            const struct Order *ord = g_EngineDb.ind_order_buckets[b];
            while (ord != NULL) {
                if (!ord->ind_order_inhash) return false;
                if (!ord->orders_inlist) return false;
                if (!ord->p_price_level) return false;
                hash_entry_count++;
                ord = ord->ind_order_next;
            }
        }
        if (hash_entry_count != g_EngineDb.ind_order_n) return false;
    }

    return true;
}
