# Walk-spec A0 inventory (was STATUS-W.md at c023bd4; the baseline for A4)

Commit: see `git log -1 -- docs/walk-spec/STATUS-W.md`   Branch: walk-spec (off `main` at `eb07b9f`)   lake build: clean (102 jobs, before and after)   sorry count under lean/Walk: 0 (no Lean files yet)

Worktree: `../uvme-walk`. No code was written in this phase. `PLAN-W.md` is the plan as received.

**The inventory changes two premises of PLAN-W §3.**
- The reference book has explicit price levels.
- The reference's matching recursion is already one resting order per call, the same granularity as the program's inner iteration.

So `Walk` can mirror both loops of the program exactly, and the equivalence (A2) should be small. Seven decisions are asked of Ara (⚑ below) before A1 starts.

---

## Done

### 1. The reference spec (`lean/MatchingEngine/`, read-only)

| Item | Where | What |
|---|---|---|
| Types | `Basic.lean` | `Price`, `Quantity`, `OrderId`, `Timestamp`, `StpGroup` are all `Nat`. Enums: `Side`, `OrderType` (5), `TimeInForce` (4), `OrderStatus` (5), `STPPolicy` (4). |
| `Order` | `Order.lean:15` | 16 fields: `id side orderType tif price : Option stopPrice qty remainingQty minQty displayQty visibleQty postOnly status timestamp stpGroup stpPolicy`. `Order.WellFormed` covers WF-1..20. |
| `Trade` | `Order.lean:35` | 9 fields: `price qty aggressorId passiveId aggressorSide aggPostOnly aggStpGroup pasStpGroup aggStpPolicy`. |
| Book | `Book.lean:13-29` | `BookState` = `bids`, `asks : List PriceLevel`, `stops : List Order`, `lastTradePrice`, `nextId`, `clock`. `PriceLevel` = `price` + `orders : List Order`, a FIFO with the head first. Bids are sorted descending, asks ascending, **so levels are explicit** and the best level is the list head. |
| Book operations | `Book.lean` | `insertAsc`/`insertDesc`, which find or create the level and append at the tail. `insertOrder` also sets `visibleQty`, `status` and `minQty := none`. `removeLevels`, `allBookOrders`, `contraLevels`/`setContraLevels`. |
| Matching | `Match.lean:39` | `doMatch (fuel) (inc) (bids asks) (trades) (tm) : MatchResult`, with fuel-bounded structural recursion on `fuel`. See below. |
| Fuel | `Process.lean:28` | `computeMatchFuel` = Σ contra `remainingQty` + contra order count + contra level count + 1. It counts quantity because an iceberg reload re-queues an order without removing it. |
| Pipeline | `Process.lean:125-218` | `processOrder`/`processCascade`/`processTriggeredStops` are mutual and fuel-bounded (`computeProcessFuel`). The phases are: 1 stops, 2 post-only, 3 FOK, 3b minQty, 4 MTL, 5 normal matching, then `dispose` and the stop cascade. `process` (`:241`) stamps `id := nextId`, `timestamp := clock`, and bumps `nextId` and `clock`. |
| Cancel | `Cancel.lean` | `findOrderOnBook` searches bids, then asks. `cancelOrder` applies `removeLevelOrder` (filter by id, drop emptied levels) to the found side. |
| Fuel lemmas | | `doMatch_fuel_stable` (`Matcher/SpecStep.lean:69`, on `main`): above `matchMeasure` (`Theorems.lean:1879`, total remaining + order count + level count), more fuel gives the same result. `processOrder_computeProcessFuel_stable` is in `TheoremsFuel.lean`. |
| WF predicates | | `Order.WellFormed` (`Order.lean`). The §13 predicates are in `Invariants.lean`: `BookUncrossed`, `NoGhosts`, `StatusConsistency`, `FIFOWithinLevel`, `NoRestingMarkets`/`MTL`/`MinQty`, `NoEmptyLevels`, sortedness, and `BookInvariant` (`:142`). `ProcessInv` (`TheoremsReachable.lean:49`) is the reachable-state bundle. |

**What one `doMatch` call does.** It handles **one interaction with the head order of the best contra level**. It returns immediately if `remainingQty = 0` or `status = cancelled`, if the contra side is empty, or if `¬canMatchPrice` against the head level. Otherwise it does one of the following:
- **Empty level:** drop it and recurse. This is unreachable under `NoEmptyLevels`.
- **Zero-visible skip:** unreachable, because resting `visibleQty = remainingQty > 0`.
- **STP, by the incoming order's policy:**
  - `cancelNewest`: set the incoming order's status to cancelled and stop.
  - `cancelOldest`: drop the resting order and recurse.
  - `cancelBoth`: drop the resting order, cancel the incoming order, and stop.
  - `decrement`: reduce both sides by `min`. The resting order is dropped if it reaches 0, and the incoming order is cancelled if it reaches 0. An iceberg reload follows, which is unreachable.
- **Normal fill:** fill `min(inc.remaining, resting.visible)` at `level.price` and append **one** trade. The resting order is then removed if it is filled; otherwise it is reloaded if it is an iceberg (unreachable), or updated to partially filled and stays at the head.

**Levels are removed inside the same call:** when the head order leaves a one-order level, the next state is `restLevels`. The price is re-tested on every call.

### 2. `processB` (`lean/Bridge/ProcessB.lean:96`, read-only)

- **Signature:** `processB (cap : Nat) (b : BookState) : Req → ResultCode × ProcessResult`, where `Req = order CRequest | cancel UInt64` and `ProcessResult = {book, trades : List Trade}`.
- **Order-request branch, in order:**
  1. `decodeOrderType = none` → `rejectedUnsupported`.
  2. `toSpec = none` (side, STP mode, qty 0, price 0 on a priced type) → `rejectedInvalid`.
  3. `qmax cap < qty` → `rejectedInvalid`.
  4. `idOnBook` → `rejectedDuplicate`.
  5. `requestMayRest r && cap ≤ bookSize b` → `rejectedCapacity`. This is pessimistic, and applies to LIMIT and POST_ONLY only.
  6. Otherwise `(postOnlyCode o b, processWithId b o)`.
- **Cancel branch:** `cancelOrder b id` gives `rejectedUnknownId` or `cancelled`.
- **Where post-only is decided: inside `process`** (Phase 2: `wouldCross` → book unchanged, else `insertOrder … false` with no matching at all). `postOnlyCode` reports the same test, and `postOnly_reject_agrees` proves the agreement.
- **`processWithId b o`** is `process {b with nextId := o.id} o`.
- **Observation:** `obsSpec x = {code, trades.map tradeObs, bookView book}`. `tradeObs` keeps `passiveId`, `aggressorId`, `price` and `qty`. `bookView` drops the order fields `postOnly`, `status`, `timestamp` and the book fields `lastTradePrice`, `nextId`, `clock`, and keeps `stops`.

**"decode"** in PLAN-W is `absBook (view s)` (`EngineDbAbs.lean:355`). It sets `stops = []`, `nextId = 1` and `clock = restingCount + 1`. Each resting order gets:
- `timestamp` = its **queue position** (from 0);
- `status` = `new_` if `remaining = qty`, else `partiallyFilled`;
- `visibleQty = remainingQty`, `displayQty = none`, `postOnly = false`.

### 3. The loops (`Program.lean:112-216`, `c/gen/matcher.c:96-163`, buy side)

**Outer loop.** It is at `Program.lean` `sideFun`, the first `.loop (.capPlus 1)`, and C lines 97–163.
- **Exit test:** `0 < rem ∧ ¬stop` (C:98). This is tested before the bound; `me_k0 == capacity+1` with the test still true traps (class 2, C:99).
- **Body:**
  1. `best = ME_asks_best()` (C:100): the level fetch.
  2. `best == NULL` → `stop = true` (C:101-102).
  3. `otype ≠ MARKET ∧ ¬(price(best) ≤ price)` → `stop = true` (C:104-105): the price test, **once per level**.
  4. Otherwise `passive = ME_queue_first(best)` (C:107), then the inner loop (C:108-155).
  5. **Cleanup:** `if ME_level_get_count(best) == 0 { ME_asks_remove(best); ME_level_free(best) }` (C:156-158).

**Inner loop.** It is at `Program.lean` `sideFun`, the second `.loop (.capPlus 1)`, and C lines 108–155.
- **Exit test:** `passive ≠ NULL ∧ 0 < rem` (C:109), with the bound check at C:110.
- **Body:** one of four branches, taken in order.

| # | Condition (C line) | Statements, in order (C lines) | Store calls | Trade |
|---|---|---|---|---|
| 1 | STP: `account ≠ 0 ∧ account = get_account(passive) ∧ stp ≠ NONE` (111), and `stp = CANCEL_NEW` (112) | `rem = 0` (113) | `order_get_account` | none |
| 2 | STP, `stp ∈ {CANCEL_OLD, CANCEL_BOTH}` (115) | `victim = passive` (116); `passive = queue_next(passive)` (117); `queue_remove(best,victim)`, `hash_remove(victim)`, `order_free(victim)` (118-120); if `CANCEL_BOTH` then `rem = 0` (121-122) | `get_account`, `queue_next`, `queue_remove`, `hash_remove`, `order_free` | none |
| 3 | STP, `stp = DECREMENT` (else, 125) | `fill = min(rem, get_remaining(passive))` (126); `rem -= fill` (127); `prem = get_remaining(passive) - fill` (128); `set_remaining(passive, prem)` (129); `nextp = queue_next(passive)` (130); if `prem = 0` then remove + hash_remove + free (131-134); `passive = nextp` (137) | `get_account`, `get_remaining` ×2, `set_remaining`, `queue_next`, [`queue_remove`, `hash_remove`, `order_free`] | none |
| 4 | no STP conflict (140) | `fill = min(rem, get_remaining(passive))` (141); `rem -= fill` (142); `prem = …` (143); `set_remaining` (144); **`me_emit(get_id(passive), id, get_price(best), fill)`** (145); `nextp = queue_next` (146); if `prem = 0` then remove + hash_remove + free (147-150); `passive = nextp` (153) | `get_account`, `get_remaining` ×2, `set_remaining`, `get_id`, `level_get_price`, `queue_next`, [remove, hash_remove, free] | one |

- **Locals used by the loops:** `rem`, `stop`, `best`, `passive`, `nextp`, `victim`, `fill`, `prem`. There is no `break` or `continue`; exits happen only through the loop tests (`rem = 0`, `passive = NULL`, `stop`).
- **Exactly one fill per inner iteration?** No. Branch 4 performs exactly one fill and emits one trade. Branches 1–3 are STP and emit no trade: branch 3 reduces both sides without a trade, branch 2 removes a resting order, and branch 1 ends the match. Every iteration touches exactly one resting order, the queue head.
- **Every continuing iteration pops the head:** branches 2, 3 and 4 with `prem = 0`. With `prem > 0`, `fill = rem`, so `rem = 0` and the loop exits. So `passive` is always the queue head while `rem ≠ 0` (clause `IInv.passive` on `main`).
- **Is the outer body "zero or more inner steps and nothing else" under decode? No, not exactly.**
  - The level fetch and the price test only read.
  - The cleanup changes the decoded book. While the emptied level is still in the tree, `absBook` decodes it as a `PriceLevel` with `orders = []`, and the cleanup removes it.
  - The reference removes a level in the same `doMatch` call in which its last order leaves.
  - So the program and the reference differ in **when** an emptied level disappears, not in whether it does. This is what `InvM` (a level may be empty) records on `main`.

### 4. The direct proof: baseline for A4 (line counts on `main`)

Each lemma's count runs from its first line to the end of its proof and excludes the doc comment. File totals include everything.

| Direct-proof lemma | File:line | Lines | Uses (reusable facts from PLAN-W §2, and its own invariant) |
|---|---|---|---|
| `inner_cancelNew` | `Inner.lean:439` | 20 | `IInv`/`SInv`, `rest_step`, `step_*` |
| `inner_cancelOld` | `Inner.lean:460` | 75 | `IInv`, `sinv_drop`, `StoreStep` drop lemmas, `LoopEnv` `ev_*` |
| `inner_dec` | `Inner.lean:634` | 120 | `IInv`, `sinv_setRem`, `sinv_drop`, `core_facts` |
| `inner_fill` | `Inner.lean:767` | 143 | the same, plus the trade |
| `inner_body` (dispatch) | `Inner.lean:911` | 14 | the four lemmas above |
| `inner_run` + `inner_loop` | `Inner.lean:930`, `:974` | 36 + 23 | `imeasure`, the loop evaluation lemmas |
| `outer_body` | `Outer.lean:228` | 141 | `OInv`, `inner_loop`, `stopX_of_best`, `free_levels_resting`, `ev_free` (40) |
| `outer_run` + `outer_loop` | `Outer.lean:379`, `:416` | 36 + 25 | `omeasure`, `OInv` |
| Resting step | `Rest.lean` (`rest_prefix` 56, `rest_run` 118, `rest_inv` 83, `rest_book` 24, `ev_newLevel` 88, `newLevel_clientInvM` 70, …) | 919 (file) | `Inv`, `stopX` clause, `StoreStep` |
| Result code / side assembly | `Accept.lean` (`side_cont` 122, `side_run` 104, `refines_accept` 61) | 649 (file) | everything above, plus `processWithId_match`/`_postOnly` |
| `matcher_refines` | `Accept.lean:624` | 13 | — |
| Invariant definitions | `IInv` 12, `SInv` 8 (`Inner.lean:187-197`), `OInv` 16 (`Outer.lean:103`) | 36 | These carry the continuation clause `spec : c.mr = rest inc own contra strades tm`. |

**Files of the direct loop proof:**

| File | Lines | What |
|---|---|---|
| `SpecStep.lean` | 507 | spec side |
| `StoreStep.lean` | 431 | store side |
| `LoopEnv.lean` | 522 | statement evaluation |
| `Inner.lean` | 996 | |
| `Outer.lean` | 440 | |
| `Rest.lean` | 919 | |
| `Accept.lean` | 649 | |
| **Total** | **4,464** | |

The entry checks and cancel are in `Refines.lean` (823) and `Cancel.lean` (1,043). The run-level theorem is in `Run.lean` (641).

**Reused infrastructure,** measured once and excluded from both sides:

| Item | Where | Lines |
|---|---|---|
| `Inv` | `Refines.lean:61` | 8 |
| `InvM` | `StoreStep.lean:392` | 8 |
| `ClientInvM` | `StoreStep.lean:160` | 11 |
| `ClientInv` | `EngineDbAbs.lean:432` | about 20 |
| decode: `absBook`, `absSide`, `absLevel`, `absQueue`, `restingOrder`, `sortLevels` | `EngineDbAbs.lean:313-362` | about 45 |
| `doMatch_fuel_stable` | `SpecStep.lean:69` | 31 |
| `processB_congr` | `Run.lean:444` | 69 |

The per-construct decode lemmas are the `StoreStep.lean` drop, set-remaining and free lemmas, and the `LoopEnv.lean` `ev_*` statement lemmas. `StoreStep` and `LoopEnv` are both "infrastructure both routes need" in PLAN-W's sense. A4 will count them once. Which of their lemmas the walk route actually uses will be recorded at A3.

**`stopX` is not a standalone fact on `main`.** It is a clause of the direct proof's outer invariant `OInv` (`Outer.lean:117`). The reusable fact is `stopX_of_best` (`Outer.lean:153`, 8 lines), and the walk route will state its own `stop` clause (⚑6).

### 5. The differential harnesses

- **`scripts/matcher_lean_diff.sh` → `lean/Matcher/CheckLean.lean`.**
  - `genReq` is a 64-bit LCG. The seed is argument 1 (default 7), then streams (400), length (60) and capacity; the script runs capacities 2, 6 and 20.
  - `runStream` steps a spec book with `processB cap b req` and the model store with `runEntry program 64 …`, and compares `obsSpec` against `(code, emitted trades, bookView (absBook s'.db))`.
  - **Swapping the oracle:** a new `lean/Walk/Check.lean` imports `Matcher.CheckLean` (for `genReq`, `matcherStep` and `Tally`) and replaces the one `processB` call. D1 compares the two spec voices; D2 compares `matcherStep` with `Walk.process`. The seeds and stream generator are the same, and the file under `lean/Matcher/` is not edited.
- **Phase 5 spec oracle:** `lean/Matcher/Oracle.lean` (exe `spec_oracle`), driven by `tests/differential/run.sh` with seeds from `gen_stream.py <seed> <len> <cap> <profile>`. The oracle is the single call `ProcessB.processB cap b q` at `Oracle.lean:71`. A `walk_oracle` exe with the same I/O would let `tests/differential/run.sh` compare it without editing the script, by diffing the two output files by hand or with a wrapper under `docs/walk-spec/`, since `tests/` is read-only.

### 6. Obstacles to `State.book : BookState`

- **Best opposite level: cheap.** It is the head of `contraLevels b side`. The reference's lists are best-first, so no search is needed.
- **Things the C tracks that the reference book does not:**
  - handles (`best`, `passive`, `nextp`, `victim`): these are pointers into the store. On the book, `best` = the head contra level and `passive` = its head order, which is derivable while `rem ≠ 0` (§3).
  - the `stop` flag: this becomes a `State` field.
  - the transiently empty level between the inner loop and the cleanup: a `PriceLevel` with `orders = []` is representable, and `absBook` produces exactly that.
- **Things the reference book tracks that the C does not:** `status`, `timestamp`, `postOnly`, `clock`, `nextId`, `lastTradePrice`. **Consequence:** decode synthesizes `timestamp` from queue position and `status` from `remaining` vs `qty`. So after a pop, the decoded timestamps of the remaining orders shift by one. The A3 relation therefore cannot be literal `decode store = st.book` with walk primitives that are the reference's list operations. It holds up to `bookView`, which drops exactly those fields (⚑2).
- **Trade:** `ME_trade_emit` receives `(maker, taker, price, qty)`, which is `tradeObs`. The reference `Trade` has 5 more fields, all derivable from the incoming order and the resting order. `State.trades : List Trade`, built as the reference builds it, keeps A2 at list equality, and the A3 relation uses `trades.map tradeObs`.

**No separate `Walk.Book` is needed.**

### 7. Proposed signatures (for approval, ⚑1–⚑7)

```lean
namespace Walk
open ProcessB

/-- The fixed data of one matching phase: the request and its spec order. -/
structure Ctx where
  r   : CRequest
  agg : Order          -- r.toSpec, with side, price, STP group/policy
  isBuy : Bool

structure State where
  book   : BookState   -- may hold one empty head contra level between inner loop and cleanup
  rem    : Nat         -- the program's `rem`, as Nat
  stop   : Bool        -- the program's `stop`
  trades : List Trade  -- emitted, in order (reference Trade, built from agg and the maker)

inductive Next | more (st : State) | done (st : State)

-- Book primitives, one per store call; all total, all on reference lists
def bestLevel   (c : Ctx) (b : BookState) : Option PriceLevel      -- ME_*_best: head of contra side
def headOrder   (c : Ctx) (b : BookState) : Option Order           -- ME_queue_first / queue_next-after-pop
def popHead     (c : Ctx) (b : BookState) : BookState              -- queue_remove+hash_remove+order_free of the head;
                                                                   -- keeps the level even if it empties
def setHeadRem  (c : Ctx) (b : BookState) (q : Nat) : BookState    -- order_set_remaining on the head
def dropEmptyBest (c : Ctx) (b : BookState) : BookState            -- tree_remove+level_free when count = 0
def insertRest  (b : BookState) (o : Order) : BookState            -- the rest block: reference insertOrder
def findById    (b : BookState) (id : Nat) : Option (Side × Order) -- hash_find/owner: reference findOrderOnBook
def removeById  (b : BookState) (sd : Side) (id : Nat) : BookState -- cancel: reference removeLevelOrder on that side
def count       (b : BookState) : Nat                              -- ME_count: bookSize

def innerStep (c : Ctx) (st : State) : Next     -- the four branches of §3, in C order
def innerRun  (c : Ctx) : Nat → State → Option State   -- exit test `head ≠ none ∧ 0 < rem`;
                                                        -- none = bound exhausted with the test true (the trap)
def outerStep (c : Ctx) (cap : Nat) (st : State) : Option State  -- fetch, stop tests, innerRun (cap+1), cleanup
def outerRun  (c : Ctx) (cap : Nat) : Nat → State → Option State -- exit test `0 < rem ∧ ¬stop`
def process   (cap : Nat) (b : BookState) (req : Req) : ResultCode × ProcessResult
  -- entry checks exactly as processOrderStmts; post-only test as sideFun's first block;
  -- rem := qty; outerRun (cap+1); rest block (including its unreachable alloc/level/hash failure
  -- returns); cancel as cancelOrderStmts. Some none from a run is mapped to a distinguished result
  -- (proved unreachable in A1 as run_fuel_sufficient).

/-- What A2 needs of the book. -/
structure WF (cap : Nat) (b : BookState) : Prop where
  stops     : b.stops = []
  nonempty  : ∀ l ∈ b.bids ++ b.asks, l.orders ≠ []
  resting   : ∀ o ∈ allBookOrders b, 0 < o.remainingQty ∧ o.visibleQty = o.remainingQty ∧ o.displayQty = none
  ids       : (allBookOrders b).map (·.id) |>.Nodup
  size      : bookSize b ≤ cap
end Walk

theorem Walk.process_obs_eq (cap b req) (hwf : WF cap b) :
    obsSpec (Walk.process cap b req) = obsSpec (processB cap b req)
```

**Check that `Inv s` implies `WF cap (absBook (view s))`,** clause by clause:
- `stops`: holds by the definition of `absBook`.
- `nonempty`: from `ClientInv.level_nonempty`.
- `resting`:
  - `0 < remaining` comes from `order_ok`;
  - `visibleQty = remainingQty` and `displayQty = none` hold by the definition of `restingOrder`.
- `ids`: from `Db.WF.hash_ids` + `hash_iff_queued`. `idOnBook_absBook` (`Refines.lean:485`) already relates hashed ids to book ids.
- `size`: from `count_le` + `count_eq` + `bookSize_absBook` (`Refines.lean:475`).

No sortedness or uncrossedness is needed. The walk and the reference both take the list head as the best level, and the order lands through the same `insertDesc`/`insertAsc`. Sortedness only matters in A3, where `absSide`'s sort makes the store's `tBest` the list head. `main` already proves that (`absSide_best`).

---

## Deviations from PLAN-W.md (proposed; none applied, since no code exists yet)

1. **The walk is nested, not flat** (`outerStep`/`innerStep`, `outerRun`/`innerRun`).
   - PLAN-W §3 flattens because "on the abstract Book there are no levels". But `BookState` has explicit levels, and the program's outer body includes a store-changing cleanup (freeing the emptied level). A flat `run` would not be one-to-one with the program.
   - With nesting, `innerStep` is exactly one inner iteration, and `outerStep` is exactly one outer iteration, cleanup included.
   - The level-cleanup timing difference moves to A2, where it is a Lean-only fact about lists.
2. **`run` returns `Option State`.** `none` means the bound is exhausted with the test still true, which is the program's `me_trap(2)`. PLAN-W's `run 0 st = st` would silently disagree with the program there. Sufficiency is then a theorem, not a convention.
3. **The A2 statement is on `obsSpec`, not full equality.** The walk does not maintain `clock`, `nextId`, `lastTradePrice`, `status` or `timestamp`, and the program has no counterpart for them. `processB_congr` is the tool where needed.
4. **The A3 relation is up to `bookView`, not `decode store = st.book`,** and it includes two derived-local clauses (`best` = head contra level, `passive` = its head order while `rem ≠ 0`). The reason is §6: decode synthesizes timestamps from queue position and status from remaining vs qty.
5. **`lakefile.toml` needs one new entry** (`[[lean_lib]] name = "Walk"`) for `lean/Walk/` to build. That is an edit to an existing file outside `lean/Walk/` and `docs/walk-spec/`.

## Findings

1. **`doMatch` already walks one order per call.** Each recursive call is one interaction with the head order of the head contra level, the same unit as the program's inner iteration. The direct proof's `inner_body` already maps one iteration to one `doMatch` unfolding. What the direct route "invented" is mainly the continuation clause `spec : mr = rest …` (in `IInv`/`OInv`) and the level-emptiness bookkeeping (`SInv.empty`/`head`, `InvM`), not a change of granularity.
2. **The only structural differences between one walk iteration and one `doMatch` call are:**
   - **(a) Level removal timing:** in the same call in the reference, but after the inner loop in the program.
   - **(b) Price test:** on every call in the reference, but once per level in the program.
   - **(c) STP cancel of the incoming order:** `status := cancelled` in the reference, `rem := 0` in the program.
   - **(d) Four reference branches unreachable on C books:** empty-level skip, zero-visible skip, iceberg reload ×2, and decrement with `reduceQty = 0`.
   - **(e) Fuel:** the reference computes quantity-based fuel, while the program's bound is `capacity + 1`.

   All five are Lean-only facts. So A2 should be much smaller than PLAN-W's "risk in the whole experiment" suggests.
3. **Expectation for A4, stated now so it can be checked:**
   - The walk route should remove the `rest`-continuation clauses and their lemmas (`rest_step` uses, the `spec` field threading, `stopT`).
   - It should not remove the store-side work that dominates `inner_fill`, `inner_dec`, `outer_body` and `rest_run`: the `InvM` preservation, frame and count facts.
   - Those facts are about the store, and both routes need them. The saving is likely to be a fraction of `Inner`/`Outer`/`Accept`, not most of the 4,464 lines.
4. **`stopX` is an `OInv` clause, not a reusable fact.** The reusable part is `stopX_of_best`.
5. **Post-only is decided inside `process`** (Phase 2), not at `processB`'s entry. The program decides it at the start of `sideFun`, after the entry checks and before matching, so the order of observable effects agrees.

## ⚑ Questions for Ara

1. **Nested walk** (`innerStep`/`outerStep`, deviation 1) instead of PLAN-W's flat `run`? Recommended: nested. It is what "one-to-one with the program" requires once levels are explicit.
2. **The A3 relation up to `bookView`,** plus the two derived-local clauses (deviation 4), instead of literal decode equality? Recommended: yes. The alternative is walk primitives that renumber timestamps and recompute status after each pop, which is transliteration of `absBook`, not of the program.
3. **A2 as equality of `obsSpec`** (deviation 3)? Recommended: yes.
4. **May A2 import the spec-only lemmas in `Matcher/SpecStep.lean`** (`processWithId_match`, `processWithId_postOnly`, `mrOf`, `afterMatch`, `step_*`)? These are Lean-only facts about `processB`, written for the direct proof but not about the store. Recommended: yes, counted in A4 as shared, with each use listed. If no, A2 re-derives about 150 lines of `process` unfolding.
5. **`run` returning `Option`** (deviation 2)? Recommended: yes.
6. **`stopX`:** the walk route states its own exit clause (no contra level crosses at `stop = true`) and reuses `stopX_of_best`. Is that acceptable as "reusing `stopX`"?
7. **The `lakefile.toml` entry** for the `Walk` library (deviation 5)? It is required to build anything under `lean/Walk/`.

## Next phase, first step

After answers to ⚑1–7, A1 begins. First comes `lean/Walk/Spec.lean` with the primitives and `innerStep`, transliterated branch by branch from C:111-153 with the `C line ↔ Lean line` table. Then come `outerStep`, `process`, and the two differentials in `lean/Walk/Check.lean`, reusing `MatcherCheck.genReq`.
