# C engine vs Lean spec: behavioural divergences

Scope: `MatchingEngine_ProcessOrder` / `MatchingEngine_CancelOrder`
(`c/src/matching_engine.c`) compared with `process` / `processOrder` / `cancelOrder`
(`lean/MatchingEngine/{Process,Match,STP,Book,Cancel,Order}.lean`). Only what C
supports: order types LIMIT, MARKET, IOC, POST_ONLY, and STP modes NONE,
CANCEL_NEW, CANCEL_OLD, CANCEL_BOTH, DECREMENT_AND_CONTINUE.

Every output below comes from a real run on the working tree as of 2026-09-27
(including the uncommitted `side` snapshot fix in `MatchingEngine_CancelOrder`).

- C driver: `driver.c`, linked against `c/src/matching_engine.c` and
  `c/src/matching_engine_gen.c`, built with `gcc -Ic/include`. It prints the return
  value of each call, every `TradeEvent`, the book (tree walk plus
  `PriceLevel_orders_First/Next`), `total_trades`/`total_volume` and
  `MatchingEngine_CheckInvariants`.
- Lean driver: `Spec.lean` (`import MatchingEngine`, `#eval main`), run with
  `lake env lean Spec.lean` from the repo root. It folds `process` over the orders,
  like `runOrders` in `Tests.lean`, and calls `cancelOrder` for cancels.
- Both drivers live in the session scratchpad, not in the repo.

Every scenario starts from an empty book (`MatchingEngine_Init` / `BookState.empty`).

## 0. Mapping used (C request → spec `Order`)

| C field | Spec field |
|---|---|
| `side` 0 / 1 | `.buy` / `.sell` |
| `order_type` LIMIT | `orderType := .limit`, `tif := .gtc`, `price := some price`, `postOnly := false` |
| `order_type` MARKET | `orderType := .market`, `tif := .ioc`, `price := none` (C price is dropped), `postOnly := false` |
| `order_type` IOC | `orderType := .limit`, `tif := .ioc`, `price := some price`, `postOnly := false` |
| `order_type` POST_ONLY | `orderType := .limit`, `tif := .gtc`, `price := some price`, `postOnly := true` |
| `qty` | `qty = remainingQty = visibleQty := qty`; `displayQty = minQty = stopPrice := none` |
| `id` | Ignored. `process` overwrites it with `b.nextId` (Process.lean:243). The C scenarios use ids 1,2,3,… in request order so both sides use the same ids. D1 is the exception. |
| `account_id`, `stp_mode` | **M1** (default, satisfies WF-16): if `account_id ≠ 0 ∧ stp_mode ≠ NONE` then `stpGroup := some account_id` and `stpPolicy := some (policy stp_mode)`, otherwise both `none`. **M2** (breaks WF-16, used only to show that no mapping works): `stpGroup := some account_id` when `account_id ≠ 0`, `stpPolicy := none` for NONE. **RAW**: `stpGroup := some account_id` even when it is 0. |
| `policy` | CANCEL_NEW→`.cancelNewest`, CANCEL_OLD→`.cancelOldest`, CANCEL_BOTH→`.cancelBoth`, DECREMENT_AND_CONTINUE→`.decrement` |
| `MatchingEngine_CancelOrder(id)` | `cancelOrder b id` (Cancel.lean:26) |

Notation in the sequences: `P(id, acct, side, type, stp, price, qty)` and `X(id)` for a cancel.

---

## 1. Behavioural divergences

### D1. Order identity: the spec ignores the caller's id; C only rejects ids that are still resting

- **C:** matching_engine.c:24-26 rejects when `EngineDb_ind_order_Find(req->id)` finds a match. The hash index only holds resting orders. C then uses `req->id` in trades (:90, :212) and in the resting order (:119, :241).
- **Lean:** Process.lean:242-247. `process` sets `id := b.nextId` and never looks at the caller's id, so it has no duplicate check. `cancelOrder` (Cancel.lean:26-32) is keyed by that spec-assigned id.

**Sequence (a), duplicate of a resting id:** `P(1,0,S,LIMIT,NONE,10,5)`, `P(1,0,S,LIMIT,NONE,11,5)`

| | Output |
|---|---|
| C | req2 returns `false`. Asks: `@10 [id=1 rem=5]` |
| Lean | Both accepted as ids 1 and 2. Asks: `@10 [id=1 rem=5]`, `@11 [id=2 rem=5]` |

**Sequence (b), id reused after its order has left the book:** `P(1,0,S,LIMIT,NONE,10,5)`, `P(2,0,B,IOC,NONE,10,5)`, `P(1,0,S,LIMIT,NONE,10,3)`, `P(4,0,B,LIMIT,NONE,10,1)`, `X(1)`

| | Output |
|---|---|
| C | All requests return `true`. Trades: `2×1 @10 q5`, `4×1 @10 q1`. `X(1)` returns `true`. Book empty. Trade history uses aggressor/passive id 1 for two different orders. |
| Lean | Trades: `2×1 @10 q5`, `4×3 @10 q1`. `cancelOrder 1` returns `none`. Asks: `@10 [id=3 rem=2]` |

**Verdict:** design choice (the C API takes client ids, the spec uses exchange ids). The refinement needs an id map, or a precondition that request ids are fresh and increasing.
Two C weaknesses remain:
- The duplicate check covers only resting orders, so ids can repeat across the trade history.
- The rejection still happens even when the id is merely stale on the spec side.

### D2. STP trigger: C ignores the resting order's STP mode

- **C:** matching_engine.c:48 / :170 trigger on `req->account_id != 0 && req->account_id == passive->account_id`. The resting order's `stp_mode` plays no part.
- **Lean:** STP.lean:10-13. `selfTradeConflict` needs `stpGroup = some g` on **both** orders. Under WF-16 (Order.lean:82) an order only has a group if it also has a policy.

**Sequence:** `P(1,7,S,LIMIT,NONE,10,5)`, `P(2,7,B,LIMIT,CANCEL_NEW,10,5)`

| | Output |
|---|---|
| C | No trade. Asks: `@10 [id=1 rem=5 acct=7]`. Order 2 is dropped. |
| Lean (M1) | `TRADE 2×1 @10 q5`. Book empty. |
| Lean (M2) | No trade. Asks: `@10 [id=1 rem=5 grp=some 7]` (matches C) |

**Verdict:** design choice. The two sides disagree on who opts in to STP: in C only the aggressor opts in, while the spec needs both groups. Under the well-formed mapping M1 the spec lets the self-trade through.

### D3. STP with incoming mode NONE and the same account: C self-trades, the spec cannot express this without WF-16

- **C:** matching_engine.c:48-78 / :170-200. No branch handles `STP_NONE`, so control falls through to the normal fill at :80 / :202.
- **Lean:** Match.lean:74-80. With a conflict and `stpPolicy = none`, `policy := inc.stpPolicy.getD .cancelNewest`.

**Sequence:** `P(1,7,S,LIMIT,CANCEL_OLD,10,5)`, `P(2,7,B,LIMIT,NONE,10,5)`

| | Output |
|---|---|
| C | `TRADE 2×1 @10 q5` (a wash trade). Book empty. |
| Lean (M1) | `TRADE 2×1 @10 q5`. Book empty (matches C). |
| Lean (M2) | No trade. Asks: `@10 [id=1 rem=5 grp=some 7]` (cancel-newest by default) |

**Verdict:** design choice. Together, D2 and D3 show that **no** single mapping of `(account_id, stp_mode)` to `(stpGroup, stpPolicy)` reproduces C:
- M1 fails on D2.
- M2 matches D2 but fails on D3, and breaks WF-16.

A refinement proof needs either:
- a spec-side "same group, no prevention" policy together with an aggressor-only trigger, or
- a C-side change.

### D4. LIMIT at price 0: C rejects it, the spec accepts it (and C accepts price 0 for IOC and POST_ONLY)

- **C:** matching_engine.c:21 rejects `order_type == LIMIT && price == 0`. There is no such check for IOC, POST_ONLY or MARKET.
- **Lean:** WF-2 (Order.lean:51) demands a positive LIMIT price, but `process`/`processOrder` (Process.lean:133-207, :242) never check `wellFormed`. Such an order rests at price 0 through `insertOrder` (Book.lean:70-78).

**Sequence:** `P(1,0,B,LIMIT,NONE,0,5)`, `P(2,0,S,MARKET,NONE,0,5)`

| | Output |
|---|---|
| C | req1 returns `false`, req2 returns `true`. No trades. Book empty. |
| Lean | req1 rests `bid @0 [id=1 rem=5]`. req2 gives `TRADE 2×1 @0 q5`. Book empty. |

**Related sequence (no divergence):** `P(1,0,B,POST_ONLY,NONE,0,5)`, `P(2,0,S,IOC,NONE,0,2)`, `P(3,0,S,POST_ONLY,NONE,0,1)`. Both sides accept the order at price 0 and trade at price 0: C gives `TRADE 2×1 @0 q2`, `bid @0 [id=1 rem=3]`, req3 `false`; Lean gives the same trade and book. This is outside WF-2 on both sides.

**Verdict:**
- The spec is permissive: it has no well-formedness gate in `process`, and its invariant theorems assume `OrderProcOk` / `Order.WellFormed`.
- C is inconsistent: it rejects price 0 only for LIMIT.
- A refinement can only cover C requests whose mapped order is well formed (price > 0 for LIMIT, IOC and POST_ONLY).

### D5. MARKET price: C ignores it, the spec honours `price` when present

- **C:** matching_engine.c:43 / :165. The price test is skipped when `order_type == MARKET`, whatever `req->price` holds.
- **Lean:** Match.lean:12-18. `canMatchPrice` uses `inc.price` if it is `some`. WF-3 (Order.lean:57) requires `none` for market orders, but `process` does not enforce WF-3.

**Sequence:** `P(1,0,S,LIMIT,NONE,10,5)`, `P(2,0,S,LIMIT,NONE,12,5)`, `P(3,0,B,MARKET,NONE,11,10)`

| | Output |
|---|---|
| C | `TRADE 3×1 @10 q5`, `TRADE 3×2 @12 q5`. Book empty. |
| Lean, mapping `price := none` | Same two trades. Book empty (matches C). |
| Lean, naive mapping `price := some 11` | `TRADE 3×1 @10 q5` only. Asks: `@12 [id=2 rem=5]` |

**Verdict:** design choice, and a proof obligation on the mapping: MARKET must map to `price := none` (and `tif := .ioc`). C has no way to represent "no price", so a price of 0 and a price of 11 mean the same thing to it.

### D6. Capacity: C rejects orders once the order pool is full; the spec is unbounded

- **C:** matching_engine.c:116-117 / :238-239 (`if (!ord) return false;`) and :130-134 / :252-256 for the level pool. The pools are allocated once in `EngineDb_Init` (matching_engine_gen.c:86-94; `ORDER_CHUNK_SIZE` = 5,000,000 and `LEVEL_CHUNK_SIZE` = 500,000 at matching_engine_gen.h:13-14). `EngineDb_order_pool_ReserveMem` is never called again.
- **Lean:** Process.lean:94-98 (`dispose`) and Book.lean:70-78. Insertion always succeeds.

**Sequence:** `P(k,0,S,LIMIT,NONE,100,1)` for k = 1 … 5,000,001, then a non-crossing `P(99999999,0,B,LIMIT,NONE,99,1)`.

| | Output |
|---|---|
| C | The first 5,000,000 are accepted. id 5,000,001 returns `false` (`pool_n=5000000`). The following non-crossing buy also returns `false`. `CheckInvariants=true`. |
| Lean | Not run at 5M. `dispose`/`insertOrder` have no failure path, and a 3-order analogue rests all three at `@100 [id=1][id=2][id=3]`. |

**Verdict:** design choice (a resource bound).
- Reasoning about the code shows the failure is always a clean reject: if matching happened and quantity is left over, at least one order slot and one level slot were freed, so allocation cannot fail after a trade.
- The refinement needs a capacity precondition, such as fewer than 5M resting orders and fewer than 500k levels.
- The hash-insert rollback at :141-150 / :263-272 cannot be reached, because the duplicate check runs first.

### D7. STP CANCEL_OLD / CANCEL_BOTH subtract the cancelled quantity from `total_qty` twice (C bug)

- **C:** matching_engine.c:55-56 / :177-178. The code does `best->total_qty -= to_cancel->remaining_qty;`, then calls `PriceLevel_orders_Remove`, which subtracts `remaining_qty` again (matching_engine_gen.c:277-281, clamped at 0). Later fills at :83 / :205 can then wrap below 0.
- **Lean:** there is no per-level aggregate. Any abstraction of `total_qty` would be the sum of `remainingQty` over the level's orders, and the cancel-oldest and cancel-both arms (Match.lean:81-97) simply drop the order.

**Sequence (a):** `P(1,1,S,LIMIT,CANCEL_OLD,10,5)`, `P(2,2,S,LIMIT,NONE,10,5)`, `P(3,1,B,LIMIT,CANCEL_OLD,10,1)`

| | Output |
|---|---|
| C | `TRADE 3×2 @10 q1`. Asks: `@10 total_qty=18446744073709551615 [id=2 rem=4]`. `CheckInvariants=false`. |
| Lean | `TRADE 3×2 @10 q1`. Asks: `@10 [id=2 rem=4]` (sum = 4) |

**Sequence (b):**
- Rest `P(1,1,S,LIMIT,CANCEL_BOTH,10,3)`, `P(2,7,S,LIMIT,CANCEL_BOTH,10,4)`, `P(3,2,S,LIMIT,CANCEL_BOTH,10,5)`, `P(4,7,S,LIMIT,CANCEL_BOTH,11,2)`.
- Then submit `P(5,7,B,LIMIT,CANCEL_BOTH,11,20)`.

| | Output |
|---|---|
| C | `TRADE 5×1 @10 q3`. Asks: `@10 total_qty=1 [id=3 rem=5]`, `@11 [id=4 rem=2]`. `CheckInvariants=false`. |
| Lean | Same trade and same orders (`@10 [id=3 rem=5]`, `@11 [id=4 rem=2]`) |

**Verdict:** C is wrong. Books and trades agree, but C's own level invariant is broken, and so is any refinement relation that includes `total_qty`. The fix is to drop the explicit subtraction at :55 and :177.

### D8. Integer width: `uint64_t` in C versus `Nat` in Lean

- **C:** four places are affected.
  - `total_qty += remaining_qty` in `PriceLevel_orders_InsertTail` (matching_engine_gen.c:254) wraps.
  - `PriceLevel_orders_Remove` (gen.c:277-281) clamps at 0, so after a wrap the value is not even correct modulo 2^64.
  - `engine->total_volume += fill_qty` (matching_engine.c:87 / :209) wraps.
  - All inputs are limited to < 2^64.
- **Lean:** Basic.lean:9-13. `Price`, `Quantity`, `OrderId` and `Timestamp` are all `Nat`.
- The per-order arithmetic cannot overflow: `rem_qty -= fill`, `remaining_qty -= fill` and the decrement all use `min` (:65, :80, :187, :202). Tested scenarios agree on books and trades.

**Sequence (a), `total_qty`:** `P(1,0,S,LIMIT,NONE,10,2^63)`, `P(2,0,S,LIMIT,NONE,10,2^63)`, `X(1)`

| | Output |
|---|---|
| C | Asks: `@10 total_qty=0 [id=2 rem=9223372036854775808]`. `CheckInvariants=false`. The sum wrapped to 0 at insert and was clamped at 0 on cancel. |
| Lean | Asks: `@10 [id=2 rem=9223372036854775808]` |

**Sequence (b), `total_volume`:** `P(1,0,S,LIMIT,NONE,10,2^63)`, `P(2,0,S,LIMIT,NONE,10,2^63)`, `P(3,0,B,MARKET,NONE,0,2^63)`, `P(4,0,B,MARKET,NONE,0,2^63)`

| | Output |
|---|---|
| C | Trades `3×1 @10 q2^63`, `4×2 @10 q2^63`. `total_volume=0`. `CheckInvariants=true`. |
| Lean | Same trades; there is no volume counter. |

**Sequence (c), spec only:** `P(·,0,S,LIMIT,NONE,2^64,2^64)`, `P(·,0,B,LIMIT,NONE,2^64,2^64+1)`. Lean trades `@18446744073709551616 q18446744073709551616` and rests `bid [id=2 rem=1]`. None of these values can be expressed in C.

**Verdict:**
- The `total_qty` handling is wrong in C: wrap on insert, then clamp on remove.
- `total_volume` is a statistic, so its wrap is a design choice.
- The domain limit is a mapping precondition: every price and quantity must be < 2^64.
- Accumulated `total_qty` per level and `total_volume` are only safe if their sums stay below 2^64.

### D9. How outcomes are reported

- **C:** `ProcessOrder` returns `bool`.
  - Returns `false` for: `qty == 0` (:20), LIMIT with price 0 (:21), duplicate resting id (:24-26), post-only cross (:34-35 / :156-157), pool exhaustion (:117, :133, :239, :255).
  - Returns `true` for: IOC or MARKET with no fill, orders dropped by STP CANCEL_NEW or CANCEL_BOTH, and partial fills.
  - `CancelOrder` returns `false` for an unknown id.
- **Lean:** `process` returns `{book, trades}` with no status (Process.lean:124-127, :242-247).
  - A rejection means the book is unchanged and the trade list is `[]`. `nextId` and `clock` still advance (:246).
  - `cancelOrder` returns `Option BookState` (Cancel.lean:26).

**Sequence:** `P(1,0,S,LIMIT,NONE,10,0)`, `P(2,0,S,LIMIT,NONE,10,5)`

| | Output |
|---|---|
| C | `false`, `true`. Asks: `@10 [id=2 rem=5]` |
| Lean | Both requests give no trades. id 1 is consumed. Asks: `@10 [id=2 rem=5]` |

A post-only cross gives the same kind of result: C returns `false`, Lean returns an unchanged book (scenario S10 below).

**Verdict:** design choice.
- Books and trades agree; only the reported status differs.
- The spec cannot tell a rejection apart from an accepted IOC with no fill, so C's return value has no spec counterpart.
- In the spec, a rejected request still consumes an id. With the D1 id alignment this makes spec ids equal to the request index, not to the C id.

### D10. NULL engine: C still changes the book but reports no trades

- **C:** matching_engine.c:85 / :207 (`if (engine)`). Matching and book changes happen regardless of `engine`.
- **Lean:** trades are always returned (Process.lean:207).

**Sequence:** `ProcessOrder(NULL, P(1,0,S,LIMIT,NONE,10,5))`, then `ProcessOrder(NULL, P(2,0,B,LIMIT,NONE,10,3))`

| | Output |
|---|---|
| C | Both return `1`. No trade is observable. Asks: `@10 [id=1 rem=2]` |
| Lean | `TRADE 2×1 @10 q3`. Asks: `@10 [id=1 rem=2]` |

**Verdict:** C API choice. The refinement should assume `engine != NULL` and `on_trade != NULL`.

### D11. Out-of-range enum values have silent meanings in C

- **C:** there is no validation.
  - Any `side != 0` takes the sell branch (:30, :152).
  - `order_type >= 4` behaves like LIMIT but skips the price-0 check (:21, :43, :115).
  - `stp_mode >= 5` behaves like NONE: a self-trade (:48-78).
- **Lean:** `Side`, `OrderType` and `STPPolicy` are closed inductives (Basic.lean:16-49), so these requests have no spec image.

**Sequence:** `P(1,7,side=2,LIMIT,NONE,10,5)`, `P(2,0,B,type=7,NONE,0,5)`, `P(3,7,B,LIMIT,stp=9,10,5)`

| | Output |
|---|---|
| C | All return `true`. Order 1 (side=2) rests as an ask. Order 2 (type=7, price 0) rests as a bid. Order 3 then produces `TRADE 3×1 @10 q5`, a self-trade between two acct-7 orders. Final book: bids `@0 [id=2 rem=5]`, asks empty. |
| Lean | Not expressible. |

**Verdict:** C should validate the enum fields. The refinement must restrict itself to valid enum values.

---

## 2. Checked and found equivalent (under mapping M1)

These are the topics the task asked about where both sides gave identical trades and books.

| Topic | C location | Lean location | Sequence | Result (both sides) |
|---|---|---|---|---|
| STP CANCEL_NEW | :49-51, :171-173 | Match.lean:78-80 | S06: rest `1(a1)@10q3, 2(a7)@10q4, 3(a2)@10q5, 4(a7)@11q2`; `5(a7) B LIMIT @11 q20` | `5×1 @10 q3`. Asks `@10 [2 rem4][3 rem5]`, `@11 [4 rem2]` |
| STP CANCEL_OLD | :52-63, :174-185 | Match.lean:81-88 | S07, same book, mode CANCEL_OLD | `5×1 q3`, `5×3 q5`. Bid `@11 [5 rem12]` |
| STP CANCEL_BOTH | :52-62, :174-184 | Match.lean:89-97 | S08, same book | `5×1 q3`. Asks `@10 [3 rem5]`, `@11 [4 rem2]` (C also has the D7 `total_qty` bug here) |
| STP DECREMENT | :64-77, :186-199 | Match.lean:98-150 | S09: S07 book + `5(a7) B @11 q20`, then `6(a7) S @11 q30`, `7(a7) B @11 q10` | `5×1 q3`, `5×3 q5`. Asks `@11 [6 rem14]` |
| STP with account 0 | :48 (`account_id != 0`) | STP.lean:10-13 | S05: `1(a0,CN) S @10 q5`, `2(a0,CN) B @10 q5` | Trade `2×1 q5` under M1. Under RAW (`stpGroup := some 0`) the spec cancels order 2 instead, so M1 must send account 0 to `none`. |
| Post-only, equal price counts as crossing | :32-37, :154-159 (`<=`, `>=`) | Process.lean:79-91 (`>=`, `<=`), :146-150 | S10: `1 S L @10 q5`, `2 B PO @10`, `3 B PO @9`, `4 S PO @9`, `5 S PO @10 q1` | Orders 2 and 4 rejected, no trades. Bid `@9 [3]`, asks `@10 [1][5]` |
| IOC and MARKET remainders dropped | :115, :237 | Process.lean:94-98 | S14: `1 S @10 q5`, `2 B IOC @10 q8`, `3 B MKT q4`, `4 B L @10 q2` | `2×1 q5`. Bid `@10 [4 rem2]` |
| MARKET with no liquidity | :42, :115 | Match.lean:49-50, Process.lean:97 | S14 req3 | No trade, nothing rests |
| Trade fields `aggressor/passive/price/qty` | :89-94, :211-216 | Match.lean:158-166 | All scenarios | Price is the passive level's price; quantity is `min(rem, passive rem)` |
| Price-time FIFO | :140 / :262 `InsertTail`, :45 `First` | Book.lean:44-66 (`orders ++ [o]`), Match.lean:63 | S16: `1 S @10 q2`, `2 S @10 q2`, `3 S @9 q1`, `4 B @10 q4` | `4×3 @9 q1`, `4×1 @10 q2`, `4×2 @10 q1`. Asks `@10 [2 rem1]` |
| Cancel of an unknown id, a partially filled order, and a repeat cancel | :279-299 | Cancel.lean:26-32 | S17: `1 S @10 q5`, `2 B IOC @10 q2`, `X(1)`, `X(1)`, `X(99)`, rest a bid, cancel it | true/some, false/none, false/none, true/some. Book empty |

---

## 3. Representational only (no effect on trades or books)

- **Trade:** the spec adds `aggressorSide`, `aggPostOnly`, `aggStpGroup` and `pasStpGroup` (Order.lean:35-44). C `TradeEvent` has only `aggressor_id`, `passive_id`, `price` and `qty` (matching_engine.h:38-43). C also keeps `total_trades` and `total_volume` counters (h:47-52).
- **Order:** the spec stores `orderType`, `tif`, `postOnly`, `status`, `timestamp`, `visibleQty`, `displayQty`, `minQty`, `stopPrice` and `stpPolicy`.
  - A resting C order stores `account_id` and `stp_mode`, but not its type.
  - Spec `status` (`new_` / `partiallyFilled`) can be derived in C from `remaining_qty < qty`.
  - `visibleQty = remainingQty` for every order C can create (there are no icebergs).
- **Timestamps and priority:** the spec's `timestamp` is `b.clock` at submission (Process.lean:243). Priority is decided by list position, never by comparing timestamps, since there are no icebergs or stops here. C has no timestamp and gets FIFO from `InsertTail`. The results agree (S16).
- **Book:** the spec also carries `stops`, `lastTradePrice`, `nextId` and `clock` (Book.lean:17-24). C carries a `total_qty` and `orders_n` for each level, plus pool and hash bookkeeping (`g_EngineDb`).
  - The spec keeps levels as sorted lists; C keeps them as unbalanced BSTs with best = max for bids and min for asks.
  - Neither side keeps empty levels: see Book.lean:82-86 and Match.lean:67-68, and matching_engine.c:108-111, :230-233, :290-297.
- **Global state:** `MatchingEngine_Init` resets the process-global `g_EngineDb` (matching_engine.c:6). Two `MatchingEngine` instances therefore share one book, while the spec's `BookState` is a value. This was not run; it is noted from the code.
- **Price for MARKET:** the spec uses `Option Price`; C uses a `uint64_t` that is ignored for MARKET (see D5 for the behavioural consequence of a wrong mapping).

## Decisions (2026-09-27)

| Entry | Decision | Status |
|---|---|---|
| D1 order ids | The refinement theorem assumes the caller never reuses an order id. With that assumption, C ids and spec ids coincide. | Assumption for Prompt 3/4 |
| D2, D3 STP trigger | C's rule is the truth. The spec changes to: a conflict exists when the incoming and resting orders share a nonzero account and the incoming mode is not NONE. The STP guarantee (INV-12) is re-proved with an "unless the incoming order opted out" clause. | Spec change in Prompt 3 |
| D4 price 0 | C rejects price 0 for every priced type (LIMIT, IOC, POST_ONLY); MARKET needs no price. | Fixed in C, tested (`test_invalid_requests_rejected`) |
| D5 MARKET price | Mapping obligation: MARKET maps to a spec order with no price. | No change |
| D6 capacity | Pool exhaustion rejects with the book unchanged. Proof obligation in Prompt 4. | No change |
| D7 `total_qty` | The generated queue operations own it on insert and remove. The duplicate client-side subtraction on the STP cancel paths is removed. Fills still adjust it in the client, because no generated operation changes an order's quantity in place. The API spec (`EngineDbApi.lean`) models `InsertTail`/`Remove` updating it. | Fixed in C, tested (`test_stp_cancel_old_keeps_level_total`) |
| D8 overflow | The refinement theorem assumes per-level totals stay below 2^64. | Assumption for Prompt 4 |
| D9 return value | The theorem states that `false` means exactly that the spec rejected the request. | Part of Prompt 4 |
| D10 NULL engine | The theorem assumes a non-NULL engine. | Assumption for Prompt 4 |
| D11 invalid enums | C rejects out-of-range `side`, `order_type` and `stp_mode`. | Fixed in C, tested (`test_invalid_requests_rejected`) |
