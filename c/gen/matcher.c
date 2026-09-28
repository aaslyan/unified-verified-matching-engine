/* Generated from lean/Matcher by Matcher.Print.program. Do not edit. */
#include "engine_db.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

static uint64_t me_ntrades;

#ifdef ME_TRAP_REPORT
void ME_TRAP_REPORT(unsigned k);
#endif
_Noreturn static inline void me_trap(unsigned k) {
#ifdef ME_TRAP_REPORT
  ME_TRAP_REPORT(k);
#else
  (void)k;
#endif
  abort();
}
static inline __attribute__((unused)) uint64_t me_add(uint64_t a, uint64_t b) {
  uint64_t r;
  if (__builtin_add_overflow(a, b, &r)) me_trap(1);
  return r;
}
static inline __attribute__((unused)) uint64_t me_sub(uint64_t a, uint64_t b) {
  uint64_t r;
  if (__builtin_sub_overflow(a, b, &r)) me_trap(1);
  return r;
}
static inline __attribute__((unused)) uint64_t me_mul(uint64_t a, uint64_t b) {
  uint64_t r;
  if (__builtin_mul_overflow(a, b, &r)) me_trap(1);
  return r;
}
static inline __attribute__((unused)) uint64_t me_div(uint64_t a, uint64_t b) {
  if (b == UINT64_C(0)) me_trap(1);
  return a / b;
}
static inline __attribute__((unused)) void me_emit(uint64_t m, uint64_t t, uint64_t p, uint64_t q) {
  if (me_ntrades >= me_add(ME_capacity(), UINT64_C(1))) me_trap(3);
  ME_trade_emit(m, t, p, q);
  me_ntrades = me_ntrades + UINT64_C(1);
}

uint64_t gen_min_u64(uint64_t a, uint64_t b) {
  (void)a;
  (void)b;
  if ((bool)(a < b)) {
    return a;
  } else {
    return b;
  }
  me_trap(4);
}

uint64_t gen_process_buy(uint64_t id, uint64_t account, uint64_t side, uint64_t otype, uint64_t stp, uint64_t price, uint64_t qty) {
  uint64_t rem = UINT64_C(0);
  bool stop = false;
  ME_LevelH best = ((ME_LevelH)NULL);
  ME_OrderH passive = ((ME_OrderH)NULL);
  ME_OrderH nextp = ((ME_OrderH)NULL);
  ME_OrderH victim = ((ME_OrderH)NULL);
  uint64_t fill = UINT64_C(0);
  uint64_t prem = UINT64_C(0);
  ME_OrderH ord = ((ME_OrderH)NULL);
  ME_LevelH lvl = ((ME_LevelH)NULL);
  bool isnew = false;
  bool ok = false;
  (void)id;
  (void)account;
  (void)side;
  (void)otype;
  (void)stp;
  (void)price;
  (void)qty;
  (void)rem;
  (void)stop;
  (void)best;
  (void)passive;
  (void)nextp;
  (void)victim;
  (void)fill;
  (void)prem;
  (void)ord;
  (void)lvl;
  (void)isnew;
  (void)ok;
  if ((bool)(otype == UINT64_C(3))) {
    best = ME_asks_best();
    if ((bool)((!(best == NULL)) && (ME_level_get_price(best) <= price))) {
      return UINT64_C(6);
    } else {
    }
  } else {
  }
  rem = qty;
  for (uint64_t me_k0 = UINT64_C(0), me_n0 = me_add(ME_capacity(), UINT64_C(1));; me_k0 = me_k0 + UINT64_C(1)) {
    if (!((UINT64_C(0) < rem) && (!stop))) break;
    if (me_k0 == me_n0) me_trap(2);
    best = ME_asks_best();
    if ((bool)(best == NULL)) {
      stop = true;
    } else {
      if ((bool)((otype != UINT64_C(1)) && (!(ME_level_get_price(best) <= price)))) {
        stop = true;
      } else {
        passive = ME_queue_first(best);
        for (uint64_t me_k1 = UINT64_C(0), me_n1 = me_add(ME_capacity(), UINT64_C(1));; me_k1 = me_k1 + UINT64_C(1)) {
          if (!((!(passive == NULL)) && (UINT64_C(0) < rem))) break;
          if (me_k1 == me_n1) me_trap(2);
          if ((bool)(((account != UINT64_C(0)) && (account == ME_order_get_account(passive))) && (stp != UINT64_C(0)))) {
            if ((bool)(stp == UINT64_C(1))) {
              rem = UINT64_C(0);
            } else {
              if ((bool)((stp == UINT64_C(2)) || (stp == UINT64_C(3)))) {
                victim = passive;
                passive = ME_queue_next(passive);
                ME_queue_remove(best, victim);
                ME_hash_remove(victim);
                ME_order_free(victim);
                if ((bool)(stp == UINT64_C(3))) {
                  rem = UINT64_C(0);
                } else {
                }
              } else {
                fill = gen_min_u64(rem, ME_order_get_remaining(passive));
                rem = me_sub(rem, fill);
                prem = me_sub(ME_order_get_remaining(passive), fill);
                ME_order_set_remaining(passive, prem);
                nextp = ME_queue_next(passive);
                if ((bool)(prem == UINT64_C(0))) {
                  ME_queue_remove(best, passive);
                  ME_hash_remove(passive);
                  ME_order_free(passive);
                } else {
                }
                passive = nextp;
              }
            }
          } else {
            fill = gen_min_u64(rem, ME_order_get_remaining(passive));
            rem = me_sub(rem, fill);
            prem = me_sub(ME_order_get_remaining(passive), fill);
            ME_order_set_remaining(passive, prem);
            me_emit(ME_order_get_id(passive), id, ME_level_get_price(best), fill);
            nextp = ME_queue_next(passive);
            if ((bool)(prem == UINT64_C(0))) {
              ME_queue_remove(best, passive);
              ME_hash_remove(passive);
              ME_order_free(passive);
            } else {
            }
            passive = nextp;
          }
        }
        if ((bool)(ME_level_get_count(best) == UINT64_C(0))) {
          ME_asks_remove(best);
          ME_level_free(best);
        } else {
        }
      }
    }
  }
  if ((bool)((UINT64_C(0) < rem) && ((otype != UINT64_C(2)) && (otype != UINT64_C(1))))) {
    ord = ME_order_alloc();
    if ((bool)(ord == NULL)) {
      return UINT64_C(5);
    } else {
    }
    ME_order_set_id(ord, id);
    ME_order_set_account(ord, account);
    ME_order_set_side(ord, side);
    ME_order_set_stp_mode(ord, stp);
    ME_order_set_price(ord, price);
    ME_order_set_qty(ord, qty);
    ME_order_set_remaining(ord, rem);
    lvl = ME_bids_find(price);
    if ((bool)(lvl == NULL)) {
      lvl = ME_level_alloc();
      if ((bool)(lvl == NULL)) {
        ME_order_free(ord);
        return UINT64_C(5);
      } else {
      }
      ME_level_set_price(lvl, price);
      ME_bids_insert(lvl);
      isnew = true;
    } else {
    }
    ME_queue_insert_tail(lvl, ord);
    ok = ME_hash_insert(ord);
    if ((bool)(!ok)) {
      ME_queue_remove(lvl, ord);
      if ((bool)(isnew && (ME_level_get_count(lvl) == UINT64_C(0)))) {
        ME_bids_remove(lvl);
        ME_level_free(lvl);
      } else {
      }
      ME_order_free(ord);
      return UINT64_C(4);
    } else {
    }
  } else {
  }
  return UINT64_C(0);
  me_trap(4);
}

uint64_t gen_process_sell(uint64_t id, uint64_t account, uint64_t side, uint64_t otype, uint64_t stp, uint64_t price, uint64_t qty) {
  uint64_t rem = UINT64_C(0);
  bool stop = false;
  ME_LevelH best = ((ME_LevelH)NULL);
  ME_OrderH passive = ((ME_OrderH)NULL);
  ME_OrderH nextp = ((ME_OrderH)NULL);
  ME_OrderH victim = ((ME_OrderH)NULL);
  uint64_t fill = UINT64_C(0);
  uint64_t prem = UINT64_C(0);
  ME_OrderH ord = ((ME_OrderH)NULL);
  ME_LevelH lvl = ((ME_LevelH)NULL);
  bool isnew = false;
  bool ok = false;
  (void)id;
  (void)account;
  (void)side;
  (void)otype;
  (void)stp;
  (void)price;
  (void)qty;
  (void)rem;
  (void)stop;
  (void)best;
  (void)passive;
  (void)nextp;
  (void)victim;
  (void)fill;
  (void)prem;
  (void)ord;
  (void)lvl;
  (void)isnew;
  (void)ok;
  if ((bool)(otype == UINT64_C(3))) {
    best = ME_bids_best();
    if ((bool)((!(best == NULL)) && (price <= ME_level_get_price(best)))) {
      return UINT64_C(6);
    } else {
    }
  } else {
  }
  rem = qty;
  for (uint64_t me_k0 = UINT64_C(0), me_n0 = me_add(ME_capacity(), UINT64_C(1));; me_k0 = me_k0 + UINT64_C(1)) {
    if (!((UINT64_C(0) < rem) && (!stop))) break;
    if (me_k0 == me_n0) me_trap(2);
    best = ME_bids_best();
    if ((bool)(best == NULL)) {
      stop = true;
    } else {
      if ((bool)((otype != UINT64_C(1)) && (!(price <= ME_level_get_price(best))))) {
        stop = true;
      } else {
        passive = ME_queue_first(best);
        for (uint64_t me_k1 = UINT64_C(0), me_n1 = me_add(ME_capacity(), UINT64_C(1));; me_k1 = me_k1 + UINT64_C(1)) {
          if (!((!(passive == NULL)) && (UINT64_C(0) < rem))) break;
          if (me_k1 == me_n1) me_trap(2);
          if ((bool)(((account != UINT64_C(0)) && (account == ME_order_get_account(passive))) && (stp != UINT64_C(0)))) {
            if ((bool)(stp == UINT64_C(1))) {
              rem = UINT64_C(0);
            } else {
              if ((bool)((stp == UINT64_C(2)) || (stp == UINT64_C(3)))) {
                victim = passive;
                passive = ME_queue_next(passive);
                ME_queue_remove(best, victim);
                ME_hash_remove(victim);
                ME_order_free(victim);
                if ((bool)(stp == UINT64_C(3))) {
                  rem = UINT64_C(0);
                } else {
                }
              } else {
                fill = gen_min_u64(rem, ME_order_get_remaining(passive));
                rem = me_sub(rem, fill);
                prem = me_sub(ME_order_get_remaining(passive), fill);
                ME_order_set_remaining(passive, prem);
                nextp = ME_queue_next(passive);
                if ((bool)(prem == UINT64_C(0))) {
                  ME_queue_remove(best, passive);
                  ME_hash_remove(passive);
                  ME_order_free(passive);
                } else {
                }
                passive = nextp;
              }
            }
          } else {
            fill = gen_min_u64(rem, ME_order_get_remaining(passive));
            rem = me_sub(rem, fill);
            prem = me_sub(ME_order_get_remaining(passive), fill);
            ME_order_set_remaining(passive, prem);
            me_emit(ME_order_get_id(passive), id, ME_level_get_price(best), fill);
            nextp = ME_queue_next(passive);
            if ((bool)(prem == UINT64_C(0))) {
              ME_queue_remove(best, passive);
              ME_hash_remove(passive);
              ME_order_free(passive);
            } else {
            }
            passive = nextp;
          }
        }
        if ((bool)(ME_level_get_count(best) == UINT64_C(0))) {
          ME_bids_remove(best);
          ME_level_free(best);
        } else {
        }
      }
    }
  }
  if ((bool)((UINT64_C(0) < rem) && ((otype != UINT64_C(2)) && (otype != UINT64_C(1))))) {
    ord = ME_order_alloc();
    if ((bool)(ord == NULL)) {
      return UINT64_C(5);
    } else {
    }
    ME_order_set_id(ord, id);
    ME_order_set_account(ord, account);
    ME_order_set_side(ord, side);
    ME_order_set_stp_mode(ord, stp);
    ME_order_set_price(ord, price);
    ME_order_set_qty(ord, qty);
    ME_order_set_remaining(ord, rem);
    lvl = ME_asks_find(price);
    if ((bool)(lvl == NULL)) {
      lvl = ME_level_alloc();
      if ((bool)(lvl == NULL)) {
        ME_order_free(ord);
        return UINT64_C(5);
      } else {
      }
      ME_level_set_price(lvl, price);
      ME_asks_insert(lvl);
      isnew = true;
    } else {
    }
    ME_queue_insert_tail(lvl, ord);
    ok = ME_hash_insert(ord);
    if ((bool)(!ok)) {
      ME_queue_remove(lvl, ord);
      if ((bool)(isnew && (ME_level_get_count(lvl) == UINT64_C(0)))) {
        ME_asks_remove(lvl);
        ME_level_free(lvl);
      } else {
      }
      ME_order_free(ord);
      return UINT64_C(4);
    } else {
    }
  } else {
  }
  return UINT64_C(0);
  me_trap(4);
}

uint64_t gen_process_order(uint64_t id, uint64_t account, uint64_t side, uint64_t otype, uint64_t stp, uint64_t price, uint64_t qty) {
  ME_OrderH dup = ((ME_OrderH)NULL);
  uint64_t r = UINT64_C(0);
  (void)id;
  (void)account;
  (void)side;
  (void)otype;
  (void)stp;
  (void)price;
  (void)qty;
  (void)dup;
  (void)r;
  me_ntrades = UINT64_C(0);
  ME_trade_reset();
  if ((bool)(!(((otype == UINT64_C(0)) || (otype == UINT64_C(1))) || ((otype == UINT64_C(2)) || (otype == UINT64_C(3)))))) {
    return UINT64_C(2);
  } else {
  }
  if ((bool)(!((side == UINT64_C(0)) || (side == UINT64_C(1))))) {
    return UINT64_C(3);
  } else {
  }
  if ((bool)(!(((stp == UINT64_C(0)) || (stp == UINT64_C(1))) || (((stp == UINT64_C(2)) || (stp == UINT64_C(3))) || (stp == UINT64_C(4)))))) {
    return UINT64_C(3);
  } else {
  }
  if ((bool)(qty == UINT64_C(0))) {
    return UINT64_C(3);
  } else {
  }
  if ((bool)((otype != UINT64_C(1)) && (price == UINT64_C(0)))) {
    return UINT64_C(3);
  } else {
  }
  if ((bool)(me_div(UINT64_C(18446744073709551615), me_add(ME_capacity(), UINT64_C(1))) < qty)) {
    return UINT64_C(3);
  } else {
  }
  dup = ME_hash_find(id);
  if ((bool)(!(dup == NULL))) {
    return UINT64_C(4);
  } else {
  }
  if ((bool)(((otype == UINT64_C(0)) || (otype == UINT64_C(3))) && (ME_capacity() <= ME_order_count()))) {
    return UINT64_C(5);
  } else {
  }
  if ((bool)(side == UINT64_C(0))) {
    r = gen_process_buy(id, account, side, otype, stp, price, qty);
  } else {
    r = gen_process_sell(id, account, side, otype, stp, price, qty);
  }
  return r;
  me_trap(4);
}

uint64_t gen_cancel_order(uint64_t id) {
  ME_OrderH ord = ((ME_OrderH)NULL);
  ME_LevelH lvl = ((ME_LevelH)NULL);
  uint64_t side = UINT64_C(0);
  (void)id;
  (void)ord;
  (void)lvl;
  (void)side;
  me_ntrades = UINT64_C(0);
  ME_trade_reset();
  ord = ME_hash_find(id);
  if ((bool)(ord == NULL)) {
    return UINT64_C(7);
  } else {
  }
  lvl = ME_order_owner(ord);
  if ((bool)(lvl == NULL)) {
    return UINT64_C(7);
  } else {
  }
  side = ME_order_get_side(ord);
  ME_queue_remove(lvl, ord);
  ME_hash_remove(ord);
  ME_order_free(ord);
  if ((bool)(ME_level_get_count(lvl) == UINT64_C(0))) {
    if ((bool)(side == UINT64_C(0))) {
      ME_bids_remove(lvl);
    } else {
      ME_asks_remove(lvl);
    }
    ME_level_free(lvl);
  } else {
  }
  return UINT64_C(1);
  me_trap(4);
}
