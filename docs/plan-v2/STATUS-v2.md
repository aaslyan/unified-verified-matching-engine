# STATUS-v2

## Phase 4 — Refinement proof (in progress: checkpoint before the matching loop)

**Date:** 2026-09-27. **Base commit:** `14e7477`. **Checkpoint commit:** see `git log -- docs/plan-v2/LOOP-INVARIANT.md`.

**Pre-proof checks (from the Phase 3 review)**
1. **Evaluation order.** No expression in the printed matcher contains more than one store call that changes state: every state-changing operation (`ext`, `call`, `emit`, `assign`) is a statement in the language, and expressions contain only pure arithmetic and store reads (`getO`, `getL`, `capacity`, `count`). The rule and the argument are in `FRAGMENT.md` ("Evaluation order"). Nested-call generation is added to the Phase 5 semantics test plan (`PLAN.md`, "Decisions after Phase 3").
2. **C differential at small capacity** (`scripts/matcher_c_capacity.sh`), capacity 8 (seeds 1–40 × 300 calls) and capacity 3 (seeds 100–139 × 300): every seed diverges, and **every first divergence is of one class**. That class is recorded here as **an expected divergence, not a failure**:
   - **Expected divergence class "capacity".** A LIMIT or POST_ONLY request arrives while the store holds `capacity` orders. The generated matcher returns the capacity code **before any trade** (the v2 rule, `processB`). The handwritten engine has no such rule: its pools hold millions of rows, so it matches and rests. The script fails on any first divergence outside this class, and on any `CheckInvariants` failure of the generated build.
3. **Lean differential kept as a regression** (`scripts/matcher_lean_diff.sh`, capacities 2, 6, 20): 27,000 steps, 0 mismatches after the Phase 4 refactor of `Program.lean`. The refactor splits the bodies into `processOrderStmts`/`cancelOrderStmts`, and `matcher.c` is byte-identical.

**Files added or changed**

| File | Change |
|---|---|
| `lean/Matcher/Logic.lean` | New. Fuel monotonicity; `Eval` (evaluation for some fuel) with one rule per statement form; `LoopRun` for bounded loops; one `runExt_*` lemma per extern operation. |
| `lean/Matcher/Refines.lean` | New. `Inv`, `CapOk`, `specStep`, `Refines`; the entry checks; the four rejections; cancel of an unknown id. |
| `lean/Matcher/Cancel.lean` | New. Cancel of a resting order, including the level-removal case; `refines_cancel`. |
| `lean/Matcher/Program.lean` | Bodies as statement lists (no change to the printed C). |
| `docs/plan-v2/LOOP-INVARIANT.md` | New. **The review point:** the matching-loop invariant. |
| `docs/plan-v2/FRAGMENT.md`, `PLAN.md` | Evaluation order; decisions after Phase 3. |
| `scripts/matcher_lean_diff.sh`, `scripts/matcher_c_capacity.sh`, `c/tests/diff_driver.c` | Regression and capacity runs; the driver prints the store size before each call. |

**Statement.** For a store `s` satisfying `Inv s`, with `CapOk S` (`capacity + 1 < 2^64`) as an explicit hypothesis rather than an `Inv` clause:

`Refines s req` := the program's entry for `req` runs to completion (for some fuel) and returns `codeOf (processB capacity (absBook (view s)) req).1`, with the emitted trades equal to the spec's trades under `tradeObs`, `bookView` of the final store equal to the spec's, and `Inv` holding afterwards.

`Inv` has these clauses:
- `WF`;
- `ClientInv`;
- live orders ↔ queued;
- live levels ↔ in a tree;
- `count = restingCount`;
- `levelsUsed = number of tree levels`;
- `count ≤ capacity`.

**Theorems proved (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`)**
- `refines_static`: unsupported and invalid requests (including `qty > Qmax`).
- `refines_duplicate`, `refines_capacity`.
- `refines_cancel_unknown`, `refines_cancel_resting`, so **`refines_cancel : Refines s (.cancel id)`** for every id.
- Supporting: the observation lemmas `bookSize_absBook`, `idOnBook_absBook`, `requestMayRest_iff`, `views_eq_of_perm` (sorted-permutation uniqueness) and `cancel_spec_view`, plus the `Inv` preservation lemmas for cancel.

**Remaining in Phase 4:** the matching loop, the resting step, and the assembly into `matcher_refines` for every request. Per the review instruction, **the loop proof waits for the review of `LOOP-INVARIANT.md`**, which has two ⚑ decisions.

**`sorry` count:** deliverables 0. Project: 2, unchanged (`lean/Bridge/ForwardSimulation.lean`, superseded by this phase's final theorem).

**Tests:** `lake build` is clean (95 jobs). Lean regression: 0 mismatches. C differential (capacity 1,000,000): 100 seeds × 1,000 calls, traces identical. `make test-gen`: 7/7.

---

## Phase 3 — Port the matcher

**Date:** 2026-09-27. **Base commit:** `f9c69e0`. **Phase commit:** see `git log -- c/gen/matcher.c`.

**Files added or changed**

| File | Change |
|---|---|
| `lean/Matcher/Program.lean` | New. The matcher AST: `gen_process_order`, `gen_process_buy`/`gen_process_sell` (one generator, `sideFun`), `gen_cancel_order`, `gen_min_u64`. |
| `c/gen/matcher.c` | New, printed (`scripts/gen_matcher.sh`; `--check` verifies it is current). 443 lines, no arrays, no pointer arithmetic. |
| `c/gen/engine_db_adapter.c`, `.h` | New. `engine_db.h` on the handwritten data layer (below the line; details under "Adapter"). |
| `c/gen/matcher_glue.c` | New. The public `MatchingEngine_*` API over the generated matcher, so the existing tests run unchanged. |
| `c/include/matching_engine_gen.h` | **Edit to the handwritten data layer:** `Order.side` and `Order.stp_mode` widened from `uint8_t` to `uint64_t` (integer rule). |
| `Makefile` | Targets `test-gen`, `gen-matcher`, and the objects of the generated build. The handwritten engine is linked into it with its matcher entry points renamed by `-D` (no source edit), for `MatchingEngine_CheckInvariants` only. |
| `lean/Matcher/Lang.lean`, `Print.lean` | Bounds `capPlus k`; `capacity`, `count`, `div`; `&&`/`\|\|` short-circuit; handle equality removed; trade sink; unused-helper attribute for clang. |
| `c/gen/engine_db.h` | `ME_capacity`, `ME_order_count`, `ME_trade_reset`, `ME_trade_emit`. |
| `lean/Bridge/EngineDbFrame.lean` | `init_empty`: the initial store has no valid handle, both counts 0, no hash, tree or queue entry. |
| `lean/Matcher/CheckLean.lean`, `Emit.lean` | New. Lean-side differential check; printer entry point. |
| `c/tests/diff_driver.c`, `scripts/matcher_c_diff.sh` | New. C-side differential against the handwritten engine. |
| `docs/plan-v2/FRAGMENT.md` | Bounds, short-circuit, no-handle section, trap policy. |

**Acceptance**
- `c/gen/matcher.c` compiles with `-std=c11 -Wall -Wextra -Werror` under gcc 13.3 and clang 19.1, each at `-O0` and `-O2`.
- **C test tally against generated matcher + handwritten data layer (`make test-gen`): 7/7 pass.** `make test` (handwritten engine, with the widened struct) also 7/7. No test fails on capacity or duplicate id: the tests stay far below capacity (1,000,000 in the glue) and the handwritten engine already rejects an id that is resting, as §4 does. So there are no ⚑ expected-failure items.

**Evidence beyond acceptance**
- **Lean differential** (`lean/Matcher/CheckLean.lean`): the matcher program under the Lean semantics on the model store against `processB`, comparing result code, trades and `bookView` after every request. **72,000 requests** (400 streams × 60, at capacities 2, 6 and 20), **0 mismatches**; all eight result codes occur (capacity rejections: 7,794 at cap 2).
- **C differential** (`scripts/matcher_c_diff.sh`): generated matcher + adapter + handwritten data layer against the handwritten engine; return value, trades, full book (every level, every order's remaining, `orders_n`, `total_qty`) and `MatchingEngine_CheckInvariants` after every call. **100,000 calls** (seeds 1000–1099 × 1,000 calls) plus 6,000 (seeds 1–20 × 300): **traces identical, invariants hold after every call.** At capacity 1,000,000 with small quantities the §4 changes never trigger, so the two engines must agree exactly, and they do.

**A bug found by the Lean differential.** The first run failed on the sixth request: the language evaluated both operands of `&&`, while C short-circuits, so the post-only test `best != NULL && crosses(best.price)` read a null handle in Lean. The semantics now short-circuits `&&` and `\|\|`, as C and AMCC's `CSubset` do. Without the check this would have surfaced as an unprovable case in Phase 4.

**Adapter (`c/gen/engine_db_adapter.c`): every function and what it maintains**

| Functions | Implementation | Maintains |
|---|---|---|
| `ME_capacity`, `ME_order_count` | adapter's capacity; `order_pool_n` | — |
| `ME_order_alloc`, `ME_level_alloc` | `NULL` iff `order_pool_n` / `level_pool_n` ≥ capacity, else the pool's alloc | the capacity law; `ME_adapter_init` reserves ≥ capacity rows in each pool so an allocation below capacity cannot fail |
| `ME_order_free`, `ME_level_free` | pool free | — |
| `ME_order_get_*`, `ME_order_set_*` (7 fields) | field access; `side`, `stp_mode` now `uint64_t` | exactness (widened, no range check) |
| `ME_order_set_remaining` | also adds `new - old` to the owner level's `total_qty` when queued | `total_qty` = sum of remaining in the level (data-layer invariant, not in the contract) |
| `ME_level_get_price`, `ME_level_set_price`, `ME_level_get_count` | fields; `orders_n` | — |
| `ME_hash_find/insert/remove` | `EngineDb_ind_order_*` | — |
| `ME_queue_insert_tail/remove/first/next` | `PriceLevel_orders_*` (which add/subtract `total_qty`) | `total_qty` on insert/remove |
| `ME_order_owner` | `p_price_level` when `orders_inlist`, else `NULL` | — |
| `ME_bids_*`, `ME_asks_*` | `EngineDb_bids_*`, `EngineDb_asks_*` | — |
| `ME_trade_reset`, `ME_trade_emit` | buffer of capacity + 1 | — |

Phase 5's contract tests must target the adapter and data layer as linked.

**Folded-in items (from review of Phase 2)**
1. Loop bounds: every loop in the matcher is `capPlus 1` (capacity + 1), and the trade buffer is `capPlus 1`; C evaluates `me_add(ME_capacity(), UINT64_C(1))`, the same quantity. No `#define` bound remains.
2. Traps stay in the shipped build (overflow, division by zero, loop bound, trade buffer).
3. "No handle": `Option` in the semantics, tested only by `isNullO`/`isNullL`; handle equality removed from the language; one law per operation says when it returns none (FRAGMENT.md, "No handle").
4. Post-only: decided in `gen_process_buy/sell` after the entry checks and before any trade, returning `rejectedPostOnly` (code 6), the code `processB` gives.
5. Adapter: table above.
6. Empty store: `init` already existed with `view init = Db.empty` and counts 0; `init_empty` now states no valid handle and no index entry.
7. Entry checks in `processB`'s order (unsupported, invalid, duplicate, capacity); a level is freed when its last order leaves (after matching, in cancel, and on the unreachable hash-insert rollback); STP triggers on nonzero equal accounts with the incoming mode ≠ NONE, as `selfTradeConflict` decides.

**Decisions settled from the repo**
- Result codes in C: accepted 0, cancelled 1, unsupported 2, invalid 3, duplicate 4, capacity 5, post-only 6, unknown id 7 (`MatcherProgram.codeOf`).
- The two `orderAlloc`/`levelAlloc` null branches after the entry checks, and the hash-insert rollback, are unreachable under `Inv`; they return `rejectedCapacity` / `rejectedDuplicate` so the program is total. Phase 4 proves them unreachable.
- `qmax` is computed in the matcher as `(2^64 − 1) / (capacity + 1)`, which needs `capacity + 1 < 2^64`: a Phase 4 assumption on the store, stated with `Inv`.
- Trades leave the matcher through `ME_trade_emit`, so `matcher.c` has no array.

**⚑ decisions needing Ara:** none.

**Deviations from the plan**
- Plan §4 said "static trade buffer" in the matcher; the buffer is in the adapter behind `ME_trade_emit`, bounded identically, so the printed matcher has no array.
- The handwritten data layer header was edited (field widening), as the Phase 2 review directed; no other handwritten C changed.
- Paths: `lean/Matcher/Program.lean`, `c/gen/`; the Lean and C differential checks were added as Phase 3 evidence ahead of Phase 5.

**Next phase:** Phase 4 — prove it. First task: state `Inv` (the coupling: `view s` well-formed, `ClientInv`, `absBook (view s)` = the spec book modulo the view, `count s` = book size ≤ capacity, levels ≤ orders with no empty level, hash ↔ book ids, `capacity + 1 < 2^64`), then the rejection-branch lemmas.

---

## Phase 2 — The matcher language

**Date:** 2026-09-27. **Base commit:** `9f68faa`. **Phase commit:** see `git log -- lean/Matcher`.

**Files added or changed**

| File | Change |
|---|---|
| `lean/Matcher/Lang.lean` | New. Syntax, values, and an executable semantics parametric in `[EngineDb S]`. |
| `lean/Matcher/Print.lean` | New. C11 printer, AMCC's dialect; only calls `engine_db.h`. |
| `lean/Matcher/Example.lean` | New. A program using every construct; `main` prints it and runs it on the model store. |
| `c/gen/engine_db.h` | New. The contract's C face. |
| `scripts/matcher_fragment_check.sh` | New. Prints the example and compiles it under gcc and clang. |
| `docs/plan-v2/FRAGMENT.md` | Every construct, its C printing, its semantics; obligations carried forward. |
| `lean/Bridge/EngineDbFrame.lean` | New. Frame laws for payload writes (follow-up item 2). |
| `lean/Bridge/EngineDbApi.lean`, `EngineDbApiLaws.lean`, `EngineDbAbs.lean` | Level totals removed from the contract; `count`/`levelsUsed` are class operations with laws (follow-up items 2, 3). |
| `lean/Bridge/ProcessB.lean` | Post-only decided in one place (follow-up item 4). |
| `lakefile.toml` | New `lean_lib Matcher`. |
| `lean/UnifiedVerifiedMatchingEngine.lean` | Imports the new modules. |

**Acceptance.** `lake build` clean (91 jobs). `scripts/matcher_fragment_check.sh`: the printed program compiles under gcc 13.3 and clang 19.1 with `-std=c11 -Wall -Wextra -Werror` ("fragment check: gcc OK", "clang OK"). The same program runs under the Lean semantics on the model store: two orders rest, a cancel removes one, a reused id is refused, and `x + 1` at the maximum is an `overflow` error.

**Theorems proved (new or changed this phase)**
- `EngineDb (AbsStore cap)`: all laws, including the new `count`/`levelsUsed` laws.
- `readOrder_writeOrder_same`, `readOrder_writeOrder_other`, `writeOrder_frame`, and the three level analogues: get after set; other rows unchanged; queues, hash, trees, validity and pool counts unchanged.
- `postOnly_reject_agrees`, `processB_postOnly_obs`, `processB_order_cases`, `toSpec_not_stop`.
- Transfer lemmas re-proved on the restructured `processB`.

`#print axioms`: `Matcher.execStmt` uses no axioms; frame laws `[propext]`; `processB` lemmas and the instance `[propext, Classical.choice, Quot.sound]` or fewer.

**`sorry` count:** 0 in every Phase 1 and Phase 2 file. Project total unchanged: 2 in `ForwardSimulation.lean` (Phase 4).

**Tests:** Lean `runAllTests` 18/18; `processB` re-run on the ten representative requests, same result codes as Phase 1.

**Follow-up items (from review of Phase 1)**
1. *Integer widths.* Done. One integer type (`u64`); enumerations are type `code`, equality only; every numeric value prints as `uint64_t`; `engine_db.h` is all `uint64_t`. The handwritten data layer's `uint8_t side, stp_mode` get widened in Phase 3 behind `engine_db.h` (edit to be listed then).
2. *Payload access.* The in-scope matcher writes order `id, account, side, stp_mode, price, qty, remaining` (resting a new order; `remaining` on each fill), writes level `price` (new level), and reads order `id, account, remaining, side`, level `price, count`, and the owner level (cancel). All are language constructs with frame laws. **Level totals:** no in-scope path reads one (`total_qty` is only ever decremented), so totals are out of the contract. The data layer maintains them privately, including in `ME_order_set_remaining`.
3. *`count`.* It is a class operation, as is `levelsUsed`, with laws: init 0; alloc +1; free −1; every other operation unchanged; alloc fails iff `capacity ≤ count`. The last is "iff `count = capacity`" under `count ≤ capacity`, which is an `Inv` clause for Phase 4 (the contract alone cannot bound an arbitrary store). No proof uses the model's lists.
4. *Post-only.* `process` does reject a crossing post-only order, so the pre-check is gone. `processB` always takes book and trades from `process`; `postOnlyCode` reports the rejection, and `postOnly_reject_agrees` proves it is exactly what `process` did (no trade; bids, asks, stops unchanged).
5. *Level-pool sizing.* Recorded in FRAGMENT.md and PLAN.md as a Phase 4 obligation: "no empty level" and levels ≤ orders go into `Inv`; Phase 3 frees a level when its last order leaves.

**Cancel and the papers.** `paper_formal_spec/paper.tex` scopes its Lean claim correctly: line 124 says "every book reachable from the empty book by a finite sequence of well-formed orders", which excludes cancels. Line 1454, "every book reachable from an empty start", is in the `process` context but should say "by `process`" to avoid being read as covering cancels. Cancel is now covered (`cancelOrder_preserves_ProcessInv`, `runB_BookInvariant`); amend still has no invariant theorem. The Zenodo follow-up is not in this repository and was not checked.

**Decisions settled from the repo**
- Loops are `while (c)` with a literal bound; exceeding it is an error, printed as a trap. `break`/`continue` are not in the language; the printer uses `break` only inside its own loop form.
- The printer does not re-check handle contracts in C (the proof covers them); it does check overflow, loop bounds and the trade buffer.
- `if` conditions print as `if ((bool)e)`: clang rejects `if ((a == b))` under `-Werror`.

**⚑ decisions needing Ara:** none.

**Deviations from the plan**
- Phase 1 files changed in Phase 2 (totals removed, pool counts as class operations, post-only restructure), at the review's request.
- Paths: `lean/Matcher/` with a new `lean_lib Matcher`; `scripts/matcher_fragment_check.sh` added to make the acceptance check repeatable.

**Next phase:** Phase 3 — port the matcher. First task: write the entry checks of `ProcessOrder` in the language, in exactly `processB`'s order (unsupported, invalid, duplicate, capacity), and the thin adapter implementing `engine_db.h` on the handwritten data layer (widen `side`/`stp_mode`; maintain `total_qty` in `ME_order_set_remaining`).

---

## Phase 1 — Contract

**Date:** 2026-09-27. **Base commit:** `c57f173`. **Phase commit:** see `git log -- lean/Bridge/ProcessB.lean`.

**Files added or changed**

| File | Change |
|---|---|
| `lean/Bridge/EngineDbApi.lean` | `Db` gains finite live sets `oLive`/`lLive`; `Db.count`, `Db.levelUsed`; four new `WF` clauses; alloc/free contracts maintain the live sets; new class `EngineDb S` (operations as functions, `capacity`, `view`, `init`, one law per operation). |
| `lean/Bridge/EngineDbApiLaws.lean` | WF preservation extended to the live sets; new section "Handle validity" (per-operation validity laws, lookups return valid handles). |
| `lean/Bridge/EngineDbAbs.lean` | Satisfiability witness: `instance EngineDb (AbsStore cap)` with every law proved. |
| `lean/Bridge/ProcessB.lean` | New: `Req`, `ResultCode`, `qmax`, `processB`, `Obs`/`obs`/`obsSpec`, `cancelOrder_preserves_ProcessInv`, transfer lemmas, reachable-state corollary. |
| `lean/UnifiedVerifiedMatchingEngine.lean` | Imports `Bridge.ProcessB`. |
| `docs/plan-v2/INVENTORY.md`, `PLAN.md`, `FRAGMENT.md` | Decisions 1 and 2 recorded; §7 supported-request list; Phase 6 linking note. |

**Theorems proved**
- `EngineDb (AbsStore cap)` instance: every contract law holds for an executable store; allocation fails exactly when `count ≥ capacity`, leaving the store unchanged.
- Handle validity: `orderAlloc_valid`/`levelAlloc_valid` (new handle valid, others unchanged), `orderFree_valid`/`levelFree_valid` (freed handle invalid, others unchanged), `*_full` (failed allocation changes nothing), frame lemmas for every other operation, and `hashFind_valid`, `tFind_valid`, `tBest_valid`, `qFirst_valid`, `qNext_valid`, `owner_valid`.
- `qmax_bound`: `(cap + 1) * qmax cap < 2^64`.
- `processB_cases`, `processB_rejected`: every rejection returns the input book and no trade.
- `cancelOrder_preserves_ProcessInv`: new; the spec had no invariant theorem for `cancelOrder`.
- Transfer: `processB_preserves_ProcessInv`, `processB_BookInvariant`, `processB_AllInv`, `processB_trades_ok` (INV-11, INV-12), `runB_BookInvariant` (every book reachable by any request sequence satisfies §13).

`#print axioms`: every transfer lemma and the instance use `[propext, Classical.choice, Quot.sound]` or fewer; no `sorryAx`, no axiom declarations.

**`sorry` count:** 0 in all five deliverable files. Project total unchanged: 2 in `ForwardSimulation.lean` (Phase 4).

**Tests:** full `lake build` clean (87 jobs); Lean `runAllTests` 18/18. `processB` evaluated on representative requests: duplicate, capacity (full and may rest), IOC when full (accepted, trades), post-only crossing, unsupported code, zero quantity, STP CANCEL_NEW, cancel known and unknown id — all as specified.

**On the transfer-lemma shape.** Every rejection and the accepted-order case are one line each: rejections return the input book, and an accepted order uses the existing `ProcessInv_step`. The cancel case is not a one-liner because `cancelOrder` had no invariant theorem in the spec; `cancelOrder_preserves_ProcessInv` (about 110 lines with its list lemmas) fills that gap once. The wrapper itself is not the cause.

**Decisions settled from the repo**
- Decision 1 is realised on C's request language: order-type codes outside LIMIT/MARKET/IOC/POST_ONLY give `rejectedUnsupported`; other malformed requests give `rejectedInvalid`.
- Check order in `processB`: unsupported, invalid (incl. `qty > qmax cap`), duplicate id, capacity, post-only crossing, then accept. The Phase 3 matcher must use the same order, since the result code is observable.
- Capacity counts resting orders plus dormant stops (`bookSize`); C never creates stops, so this is the resting-order count.
- The level pool uses the same `capacity` as the order pool (`levelAlloc` fails iff `levelUsed ≥ capacity`). Levels in the book are non-empty, so they never exceed resting orders.
- `Obs` as proposed in INVENTORY §2; the matcher side `obs` decodes its final store with `absBook`.

**⚑ decisions needing Ara:** none new.

**Deviations from the plan**
- `processB` is in `lean/Bridge/ProcessB.lean`, not `Spec/ProcessB.lean`: it takes the C request type, which lives in `Bridge`, and the repository has no `Spec/` directory.
- The abstract model never reuses a freed handle; the contract allows reuse, and nothing proved depends on either.
- `FRAGMENT.md` exists early, holding only the Decision 2 note; Phase 2 fills it.

**Next phase:** Phase 2 — the memory-free matcher language. First task: check whether AMCC's fixed-width arithmetic functions (`evalBin` and friends) import without the `CSubset` memory model; if not, define the language's own minimal arithmetic.

---

## Phase 0 — Inventory and freeze

**Date:** 2026-09-27. **Base commit:** `4811a13`. **Phase commit:** see `git log -- docs/plan-v2`.

**Files added or changed**
- `docs/plan-v2/INVENTORY.md` (deliverable)
- `docs/plan-v2/PLAN.md`: plan v2 verbatim, so later sessions read it from the repo
- `docs/plan-v2/STATUS-v2.md` (this file)
- `docs/c-verification-plan.md`: marked superseded by v2

**Theorems proved:** none (inventory phase).

**`sorry` count**
- Deliverables: none (documents only).
- Project: 2, both in `lean/Bridge/ForwardSimulation.lean` (`insert_forward_sim`, `match_step_forward_sim`). Both are replaced in Phase 4.

**Tests:** not run; no code changed. `lake build` is clean at the base commit (86 jobs).

**Decisions settled from the repo**
- In scope: limit (GTC), market (IOC), IOC limit, post-only, cancel, all four STP modes plus NONE.
- `process` has no result code and no trade timestamps. `Obs` is proposed in INVENTORY §2, with `rejectedPostOnly` decided by the same test `process` uses.
- Two account-0 orders may trade, in both the spec and C.
- EngineDb gaps for Phase 1: no finite live set (so no `count`), allocation may fail at any time, no class `EngineDb S`, and no functional instance.
- `CSubset` programs cannot allocate: the heap exists in the memory model, but no syntax reaches it.
- `CSubset` arithmetic wraps; §4 wants overflow as an error.

**⚑ decisions needing Ara**
1. Spec-only request types (FOK, DAY, stop limit and stop market, market-to-limit, iceberg, minimum quantity, amend): confirm they stay out of the generated matcher, per the §4 default. This does not block Phase 1, because Phase 1's `processB` takes the C request type, which cannot express them.
2. Where the memory-free fragment lives. Extending `CSubset` changes the AMCC dependency, where 35 files import it and its proofs recurse over `Stmt`/`Expr`. The alternative is a separate language in this repository. **Blocks Phase 2**; not Phase 1.

**Deviations from the plan**
- `PLAN.md` was added so the plan persists across sessions; this is not in the Phase 0 deliverable list.
- STATUS lives at `docs/plan-v2/STATUS-v2.md`, next to the other v2 documents.

**Next phase:** Phase 1 — Contract. First task: add a finite live set to `Db` (so `count` is computable), then the class `EngineDb S` with `capacity`, `count`, and allocation that fails iff full.
