# Walk-spec STATUS — Phase A3a (WF from Inv; the inner loop refines the walk)

Commit: see `git log -1 -- docs/walk-spec/STATUS-W.md`   Branch: walk-spec   lake build: clean (113 jobs, no warnings in `lean/Walk/`), before and after   sorry count under lean/Walk: 0

A0, A1 and A2 records: `A0-INVENTORY.md`, `A2-STATUS.md`; the A1 status is in git history at `d9e83c8`.

**Summary:**
- `WF_of_Inv` is proved. Every clause follows from `main`'s `Inv` + `CapOk`, so there is no ⚑.
- The inner body lemma `w_inner_body` is proved with the identity relation of PLAN-W §4 A3.
- **No continuation-style clause was needed,** which confirms the prediction.
- The inner loop lemma `w_inner_loop` is proved in both directions: walk `some` → the program runs to a related state; walk `none` → the program has no run (bound exhausted, `me_trap(2)`, or buffer full, `me_trap(3)`).
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Done

| File | Lines | Contents | A4 category |
|---|---|---|---|
| `lean/Walk/WFInv.lean` | 136 | `WF_of_Inv` and two generic list lemmas | walk-route-specific; the direct route states no `WF` |
| `lean/Walk/LogicInv.lean` | 146 | Inversion rules for `main`'s program logic: `loopRun_of_eval`, `Eval.seq_inv`, `Eval.ite_inv`, `Eval.emit_inv` | infrastructure; used only by the trap direction, which the direct route does not prove |
| `lean/Walk/RefineInner.lean` | 866 | `WR`; `book_step`; the head facts; `invM_drop`/`invM_setRem`; `WCore`; `w_inner_body`; `w_inner_body_trap`; `w_inner_run`/`w_inner_run_none`; `w_inner_loop` | walk route, A3 |

### 1. `WF_of_Inv`, clause by clause

`Inv s → CapOk S → WF (capacity S) (absBook (view s))`:

| `WF` field | From |
|---|---|
| `cap64` | `CapOk` |
| `stops` | `absBook`: `rfl` |
| `count` | `bookSize_absBook` + `Inv.count_eq` + `Inv.count_le` |
| `nonempty` | `ClientInv.level_nonempty` through `absQueue_ne_nil` |
| `resting` | `ClientInv.order_ok` (positive remaining); the rest by `restingOrder`'s definition |
| `ids` | `Db.WF`: `tree_nodup`, `tree_disjoint`, `queue_nodup`, `queue_unique` (the resting handles are distinct), `hash_ids` + `hash_live` + `ClientInv.hash_iff_queued` (distinct handles have distinct ids), and the decoded id list is a permutation of the handles' ids |
| `sorted` | `absSide_pairwise` |

### 2. The relation, and the answer to the prediction

`WR r isBuy l s L ts st`:

| Clause | Kind |
|---|---|
| `book : bookView (absBook (view s)) = bookView st.book` | identity |
| `rem : L.rem.toNat = st.rem` | identity |
| `stop : L.stop = st.stop` | identity |
| `trades : ts = st.trades.map tradeObs` | identity |
| `bestL : L.best = some l` | derived local |
| `passive : L.rem ≠ 0 → L.passive = (queue l).head?` | derived local |
| `inv : InvM s l`; `mem`: `l` in the contra tree; `best`: `l` best there | store-side (`main`'s `InvM`, imported) |

**Continuation-style clause needed: no.**
- Nothing in `WR` mentions `doMatch`, `rest`, a final result, or any reference state.
- Also absent are the direct `IInv`'s `aggr`/`shape` (the incoming order against `rem`) and `tbound` (the trade-buffer bound).
- `tbound` is not needed because the walk's emit test (`trades.length < cap + 1`) and the program's (`ts.length < capacity + 1`) are the same test once `ts = st.trades.map tradeObs`. So the program traps exactly where the walk does, and nothing has to be bounded.
- The empty head level needs no clause either. The decoded store and the walk's book both keep it, so `bookView` equality covers it literally.

### 3. The inner body: `w_inner_body`

From `WR … st`, with the inner test true and `innerStep st = some st'`, the program's `innerBody` ends normally in a state related to `st'` by `WR`.
- Each of the six branches is: unfold `innerStep` (rewriting `tBest`/`qFirst` with the head facts), follow the same branch in the program with `main`'s `ev_*` statement lemmas, and re-establish `WR`.
- The book clause comes from one generic lemma, `book_step`: a `Frame` step on level `l` and a head-level edit on the walk give the same view if the new head levels have the same view. The two head-level views are `view_drop` and `view_setRem`.
- The STP test is related by `acct_iff`: the walk's `getAccount` against the row's `account`.

### 4. The trap and the loop

- **`w_inner_body_trap`:** where `innerStep st = none` (full trade buffer), the program's body has no run of any outcome. The proof runs `ite`/`seq` inversion through the fill block to the `emit`, whose inversion contradicts the full buffer.
- **`w_inner_run` / `w_inner_run_none`:** induction on the budget. It mirrors `innerRun`'s recursion one for one, so no measure is needed; the direct route needs `imeasure`.
- **`w_inner_loop`:** at the bound `capacity + 1`:
  - `innerRun … = some st'` → the loop statement `Eval`s to a related state;
  - `innerRun … = none` → the loop statement has no run.

  The second half uses `loopRun_of_eval`: a successful loop is a `LoopRun` of its budget, so with the budget spent and the test true there is none.

## A3 lemmas: mechanical or not (the experiment's main output)

"Mechanical" means the proof goes through by unfolding the walk and evaluating statements, with no statement or idea specific to the proof. The obstacles hit in the mechanical rows were name resolution (`Walk.count` shadowing `EngineDb.count`), projections of `wctx`, and Lean syntax, not mathematics.

| Lemma | Lines | Mechanical? | Note |
|---|---|---|---|
| `WR` (definition) | 13 | — | the identity relation; written down, not invented |
| `bookView_sides`, `sideL_absBook` | 10 | mechanical | unfolding |
| `book_step` | 43 | **not** | the one generic idea of A3a: a frame step at level `l` preserves the view outside `l`'s head position (`absSide_best` + `Frame.restSide_eq` + `Frame.absSide_other`). Stated once, used six times |
| `wr_split` | 22 | mechanical | decompose `WR.book` with `absSide_best` |
| `WHead`, `whead` | 42 | mechanical | collect the head facts; mirrors `main`'s `head_facts` minus its spec part |
| `acct_iff` | 16 | mechanical | case split on account 0 |
| `invM_drop`, `invM_setRem` | 39 | mechanical | store-side; `main`'s `sinv_drop`/`sinv_setRem` restricted to `InvM` |
| `best_frame`, `view_drop`, `view_setRem` | 45 | mechanical | frame and list congruence |
| `WCore`, `wcore` | 57 | mechanical | `main`'s `core_facts` minus its spec part |
| `ev_innerCond_walk` | 27 | mechanical | the inner test, both sides |
| `w_inner_body` | 303 | mechanical | six branches, each an `ev_*` chain plus `WR` re-establishment; nothing to invent |
| `seq_through`, `w_inner_body_trap` | 68 | mechanical | inversion down the fill block |
| `w_inner_run`, `w_inner_run_none`, `w_inner_loop` | 103 | mechanical | induction mirroring `innerRun` |
| `WF_of_Inv` (+ list helpers) | 136 | **not quite** | the `ids` clause needs a short argument: distinct handles, then the hash makes their ids distinct. The other clauses are mechanical |
| `LogicInv` (4 inversion rules) | 146 | mechanical, infrastructure | `loopRun_of_fold` took three attempts, over unfolding hygiene, not content |

**A3a on the walk route:** apart from `book_step` (43 lines) and the `ids` clause of `WF_of_Inv`, every lemma is mechanical.

**The same ground on the direct route** (`Inner.lean`):
- `IInv`/`SInv`/`OCtx.Ok` carry the continuation `spec`, `aggr`, `shape`, `tbound` and `SInv.empty`/`head` (the reference contra list against the store). Each branch lemma re-establishes each of them.
- `inner_cancelNew` 20, `inner_cancelOld` 75, `inner_dec` 120, `inner_fill` 143, `inner_body` 14, `inner_run` + `inner_loop` 59: about 431 lines. That is before the shared `head_facts`/`sinv_*`/`core_facts` (about 250), in a 996-line file.
- The walk-route counterpart is `w_inner_body` 303 + loop and trap 171 + relation and helpers about 390, for 866 lines in total. That includes the trap direction, which the direct route does not have.

## Running totals (Ara's A4 addition, stated now)

| Route | Files | Lines |
|---|---|---|
| **Direct, route-specific** | `Inner` 996 + `Outer` 440 + `Rest` 919 + `Accept` 649 | **3,004** |
| **Walk, route-specific so far** | `Spec` 432 + `Basic` 335 + `EquivEntry` 444 + `EquivMatch` 680 + `Equiv` 417 + `RefineInner` 866 | **3,174** |
| Walk, extra: `WF_of_Inv` | `WFInv` 136 | 136 |
| Walk, extra: trap direction (language infrastructure) | `LogicInv` 146 | 146 |
| Not counted | `Check.lean` 138 (evidence); `SpecStep`, `StoreStep`, `LoopEnv`, `Logic`, `Refines`, `Cancel`, `Run` (shared) | — |

The walk-route totals exclude A3b: outer body and loop, entry, cancel, rest and result code, and the corollary.

## Shared lemmas from `main` used in A3a (all by import)

- **`StoreStep`:** `InvM`, `Frame` (+ `restSide_eq`, `absSide_other`, `levelPrice_eq`), `dropDb`, `setRemDb`, `frame_drop`, `frame_setRem`, `drop_clientInvM`, `drop_orders_resting`, `drop_restingCount`, `setRem_clientInvM`, `absSide_best`, `restSide`, `levelView_absLevel`, `ordV`.
- **`LoopEnv`:** `Loc`, `mkSt`, `innerBody`, `innerCond`, `fillStmts`, `cancelOldBlock`, `umin`, and the `ev_*` statement lemmas (`ev_innerCond`, `ev_stpCond`, `ev_stp_eq`, `ev_oldBoth`, `ev_rem0`, `ev_victim`, `ev_qNextP`, `ev_qNextN`, `ev_remove`, `dropS_facts`, `ev_min`, `ev_subRem`, `ev_prem`, `ev_setRem`, `ev_emit`, `ev_premWhen_zero`/`pos`, `ev_passiveNext`, `boundVal_trade`, `lsimp`).
- **`Logic`:** `Eval` and its rules, `LoopRun`, `Eval.loop`, `Eval.det`, `execStmt_loop_finish`, `foldl_loopStep_*`.
- **`Inner.lean`:** its store and view helpers, none carrying the continuation: `head_decomp`, `RowView`, `rowView_of`, `view_update`, `ordV_congr`, `qNext_head`, `dropDb_setRem`.
- **`Refines`:** `Inv`, `CapOk`. **`EngineDbAbs` / `Refines` / `Cancel`:** `absQueue_ne_nil`, `mem_absQueue`, `bookSize_absBook`, `absSide_pairwise`, `sortLevels_perm`, `mem_sortLevels`, `rowOf`.

## Deviations from PLAN-W.md (what, why)

1. **`WR` carries three store-side clauses:** `InvM`, `l ∈ tree`, `l` best. They are facts about the store, not about the walk or the reference. The direct route has them too, in `SInv` and `OCtx.Ok`.
2. **Two infrastructure files beyond PLAN-W §4:**
   - `WFInv.lean`: needed by the corollary. The direct route states its relation on `absBook` directly and never needs `WF`.
   - `LogicInv.lean`: the trap direction Ara asked for needs converse rules the program logic did not have.
3. **The trap correspondence is stated as "no successful run"** (`¬ Eval …`), since `Eval` only describes successful runs. The error value itself (`.bound` vs `.tradeBuffer`) is not identified.

## Findings

1. **Prediction confirmed.** The inner loop needs no continuation clause. The relation is identity on the walk's fields, plus two derived locals, plus store facts.
2. **The direct route's trade-buffer bound (`IInv.tbound`) disappears.** It becomes literal equality of the emit test on both sides. A1's potential argument (trades + contra orders ≤ cap) is still needed, but only once, on the walk (`run_fuel_sufficient`), and not inside the refinement.
3. **The empty head level between the inner loop and the cleanup needs no bookkeeping clause.** The direct route has `SInv.empty`/`head`. Here, decoded store and walk both hold the empty level, and the view equality covers it.
4. **The inner loop needs no measure.** The walk's `innerRun` has the program's budget, so the induction is on the budget itself; the direct route has `imeasure` and its decrease proofs.
5. **What remains is store-side and statement evaluation.** Of `RefineInner`'s 866 lines:
   - about 110 relate store to walk (`book_step`, `wr_split`, `view_drop`, `view_setRem`, `acct_iff`);
   - about 140 are store-side (`InvM`, `WCore`, frames);
   - the rest is statement evaluation and assembly.

   This split feeds A4's three-way classification.

## ⚑ Questions for Ara

None.

## Next phase, first step (A3b)

1. `lean/Walk/RefineOuter.lean`. The outer body (level fetch, stop tests, `matchBlock` = `qFirst` + inner loop + `freeStmt`) against `outerStep`, with `InvM` → `Inv` at the cleanup. The relation outside an iteration is `WR` without `l`: `Inv s`, `bookView` equality, `rem`, `stop`, `trades`.
2. It uses `main`'s `free_clientInv`, `free_absSide`, `free_restingCount` and `stopX_of_best`, if the walk's stop clause needs it.
3. Then the outer loop (`w_outer_loop`), the entry checks, post-only, rest, cancel, `Walk.refines`, and `matcher_refines` verbatim.
