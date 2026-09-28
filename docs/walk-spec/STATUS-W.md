# Walk-spec STATUS — Phase A2 (equivalence with the reference)

Commit: see `git log -1 -- docs/walk-spec/STATUS-W.md`   Branch: walk-spec   lake build: clean (default target, now including `Walk`: 110 jobs), before and after   sorry count under lean/Walk: 0

**`Walk.process_obs_eq` is proved** (`lean/Walk/Equiv.lean`). On a `WF` book the walking spec does not trap, and its `obsSpec` equals `processB`'s. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

The stronger `Walk.process_agree` gives:
- the same result code;
- the trades as reference `Trade`s, equal element for element;
- the book equal to `processB`'s up to `nB`, the view as a spec object.

Step 3 (one walk step against one reference step) was not blocked. It went through in this session, in the order asked: entry checks and cancel, then fuel, then the step.

## Ara's A1 decisions, carried out

1. **`Walk` is in `defaultTargets`.** `lakefile.toml` now has exactly two edits outside `lean/Walk/` and `docs/walk-spec/`:
   - the `[[lean_lib]] name = "Walk"` entry, now `globs = ["Walk.+"]`;
   - `"Walk"` added to `defaultTargets`.

   The `#eval` runner moved to `docs/walk-spec/CheckRun.lean` so the glob does not build it.
2. **No `walk_oracle`.** It is kept as an A4 option.
3. **Planted-bug check.** `MUTANT=1|2 docs/walk-spec/walk_diff.sh` plants the mutant in `lean/Walk/Spec.lean`, runs `genReq` seed 7, 40 × 60, cap 6, and succeeds only if the differential fails. It refuses to run on a modified `Spec.lean` and restores the file on exit.

   | Mutant | Change | Where | Caught by |
   |---|---|---|---|
   | 1 | `CANCEL_BOTH` does not zero `rem` | `innerStep`, the `stpMode = 3` line (C:121-122; currently Spec.lean:196) | D1 (14 mismatches) and D2 (14) |
   | 2 | the level cleanup never fires (`levelCount best' = 7`) | `outerStep` (C:156; currently Spec.lean:236) | D1 (11) and D2 (11); 29 traps (`me_trap(2)`: bound exhausted on the undropped empty level) |

   The script prints the line it changed, so the record follows the file.
4. **Phase 3 capacity coverage:** recorded under Findings, as a note for `main`'s EVIDENCE.md, not a change on this branch.

## Done

| File | Lines | Contents |
|---|---|---|
| `lean/Walk/EquivEntry.lean` | 444 | `WF`; `Agree`; `processOrder_eq`, `processOrder_entry` (the entry checks); `walkRemove_eq`, `cancel_eq` (cancel) |
| `lean/Walk/EquivMatch.lean` | 680 | `normC`, `CO`, `IR`; `conflict_iff`, `policy_of`, `canMatch_iff`, `mkTrade_eq`; **`step_sim`**; `innerStep_frame`; `inner_sim`; `OW`, `outerStep_OW`, `outer_sim` |
| `lean/Walk/Equiv.lean` | 417 | rest-block lemmas (`modAt_eq_map`, `modAt_insLevel`, `nO_restOrder`, `rest_found`/`rest_fresh`/`rest_none`); `mr_eq`, `postOnly_iff`; `sideProc_agree`; **`process_agree`**, **`process_obs_eq`** |

### 1. Entry checks and cancel

- **`processOrder_entry`.** Every entry rejection gives exactly `processB`'s result. An order that passes the checks runs `sideProc` where `processB` runs `(postOnlyCode o b, processWithId b o)`.
  - It uses `main`'s `processB_static` and `processB_after_static` for the request-only checks.
  - It uses `hashFind_isSome` (the walk's `hashFind` is `idOnBook`) and `count_eq_bookSize` (the two counts agree on a stop-free book).
- **`cancel_eq`.** `Walk.cancel b id = processB cap b (.cancel id)`, **exactly**, not only through the view.
  - The core is `walkRemove_eq`: `modAt`/`eraseP` followed by the conditional `eraseP` of the emptied level equals `removeLevelOrder`.
  - It holds on a side with distinct prices, no empty level and unique ids. The proof splits the side at the owner level as `A ++ l :: B`.

### 2. Fuel

- The walk's fuel `cap + 1` suffices: `outerRun_ok` (A1).
- The reference is taken at its own fuel through `rest_start`, via `mr_eq` and `computeMatchFuel_gt_matchMeasure`. That is `main`'s `doMatch_fuel_stable`, through `SpecStep`.
- So the two loops are related at sufficient fuel on both sides, and no fuel equation is needed.

### 3. One walk step is one reference step: `step_sim`

At head level `L :: R` with head order `p :: os`, one `innerStep` and one `doMatch` call keep the reference's remaining computation (`MatcherSpec.rest`).
- **Six branches:** `CANCEL_NEW`, `CANCEL_BOTH`, `CANCEL_OLD`, decrement (full or partial), fill (full or partial).
- **Each branch uses the matching `MatcherSpec.step_*` lemma,** closed by `rest_step` (measure `mm_drop1`) or `rest_step_done`.
- **The bridging facts** say the request's tests are the reference's:
  - `conflict_iff`: the walk's STP test is `selfTradeConflict`;
  - `policy_of`: the STP mode maps to `stpPolicy`;
  - `canMatch_iff`: the price test is `canMatchPrice`;
  - `mkTrade_eq`: `mkTrade` is `fillTrade`.

The two sides differ only in bookkeeping, and `step_sim` states exactly these three differences:

| | Walk | Reference | Stated by |
|---|---|---|---|
| (a) An emptied level | kept until the outer cleanup | dropped in the same call | `normC`: the reference's contra side is `normC` of the walk's |
| (b) Cancelling the incoming order | `rem := 0` | `status := cancelled` | `IR` (`rem = 0 → done`; `rem > 0 → remainingQty = rem ∧ ¬cancelled`) |
| (c) After a partial fill | the maker has no status | the maker is `partiallyFilled` | the contra sides agree up to `nL`, and the match is over |

**The loops:**
- `inner_sim` folds `step_sim` over `innerRun` by induction on the bound. `innerStep_frame` supplies the walk-side facts: only the head level changes, and its ids only shrink.
- `outerStep_OW` and `outer_sim` fold one outer iteration (level fetch, stop tests, inner loop, cleanup) under the invariant `OW`:
  - the own side and the stops are the input's;
  - the contra-side ids form a sublist of the input's;
  - while `rem > 0`: no empty level and only good orders;
  - `rel`: while the loop runs, the final reference result is the remaining computation from the related state; after exit, it is that state's `term`.

### 4. Assembly: `sideProc_agree`, then `process_agree`

- **Post-only** (`postOnly_iff`): the walk's test is `postOnlyCode`'s.
- **Start state:** `OW` holds at `(b, qty, false, [])` against `mrOf b o` (`mr_eq`).
- **Exit:** `outerRun_final` gives the terminal form.
- **Rest block against `dispose`:**
  - The book matches when the remainder rests at an existing level (`modAt_eq_map` + `insSpec_exists`) and at a fresh one (`modAt_insLevel` + `insSpec_fresh`).
  - The view of the resting order matches (`nO_restOrder`).
  - The no-rest case uses `dispose_norest`.
- **The three failure returns of the rest block are dead on `WF` books,** each proved:
  - order pool full: `count` after matching ≤ `count b` < `cap`;
  - level pool full: levels ≤ orders on both sides;
  - hash duplicate: after matching, the ids form a sublist of the input's, and the id was not on the input.

### Evidence re-run after the A2 edits to `Spec.lean`

- The full differential passes: 144,000 steps, D1 0, D2 0, 0 traps, 10,279 pessimistic capacity rejects.
- Both mutants are caught.

### `WF` and `Inv`: paper check; the Lean proof is A3 infrastructure

| `WF` field | From `Inv s` and `CapOk S` for `absBook (view s)` |
|---|---|
| `cap64` | `CapOk` |
| `stops` | `absBook` |
| `count` | `count_eq` + `count_le` + `bookSize_absBook` |
| `nonempty` | `ClientInv.level_nonempty` |
| `resting` | `order_ok` (positive remaining) and `restingOrder`'s definition (`visibleQty = remainingQty`, `displayQty = none`, side from the tree) |
| `ids` | `Db.WF.hash_ids` + `queue_unique` + `hash_iff_queued` |
| `sorted` | `absBook_AllInv` (sorted sides) with `pairwise_of_bidsSorted`/`pairwise_of_asksSorted` |

A3 will prove `WF_of_Inv` in `lean/Walk/` and mark it as infrastructure.

## Shared lemmas from `main` (all spec-side: no store, no program), with uses

| Source | Lemmas | Used in |
|---|---|---|
| `SpecStep.lean` (approved, A0 ⚑4) | `MatcherSpec.rest`, `rest_step`, `rest_step_done`, `rest_start`, `rest_done`, `rest_empty`, `rest_noprice`, `dm`, `term`, `drop1`, `AtHead`, `step_cancelNew`/`Old`/`Both`, `step_decrement_full`/`part`, `step_fill_full`/`part`, `fillTrade`, `decInc`, `mm_drop1`, `done_of_cancelled`, `mrOf`, `o1Of`, `afterMatch` | `step_sim`, `inner_sim`, `outerStep_OW`, `mr_eq`, `sideProc_agree` |
| `Run.lean` | `nB`, `nL`, `nO`, `bookView_iff`, `pwi_cases`, `postOnlyCode_cases`, `insertDesc_nL`, `insertAsc_nL` | `Agree.obs`, `sideProc_agree` |
| `Accept.lean` | `SpecOrd`, `specOrd_of`, `sideOf_isBuy`, `term_bids_asks`, `restOrd`, `dispose_rest`, `dispose_norest`, `Static`, `static_of` | `CO_of`, `postOnly_iff`, `nO_restOrder`, `sideProc_agree`, `process_agree` |
| `Refines.lean` | `staticCode`, `processB_static`, `processB_after_static`, `requestMayRest_iff` | `processOrder_eq`, `processOrder_entry`, `sideProc_agree` |
| `Inner.lean` | `IncShape` and its accessors, `canMatch_shape` | `IR`, `step_sim` |
| `Rest.lean` | `insSpec`, `insSpec_fresh`, `insSpec_exists` | `sideProc_agree` |
| `Cancel.lean` | `removeLevelOrder_eq`, `dropStep` | `walkRemove_eq` |
| `MatchingEngine/Theorems.lean` | `computeMatchFuel_gt_matchMeasure` | `mr_eq` |

The files other than `SpecStep.lean` go beyond what A0 ⚑4 approved (⚑1 below). Every lemma listed is a statement about `processB`, `process`, `doMatch` or reference lists. None mentions the store or the program.

## Deviations from PLAN-W.md (what, why)

1. **`WF` is stronger than proposed at A0.** It adds three fields:
   - `sorted`: strict price order on each side. Needed to insert the remainder at an existing level (`insertDesc` finds the same level as `tFind` only on a sorted side), and by cancel (distinct prices).
   - `resting.side`: needed by cancel, which removes the emptied level from the tree of the order's side.
   - `cap64`: `Walk.process` traps on a `cap + 1` that does not fit `uint64_t`.

   A0's claim that no sortedness would be needed was wrong. `Inv` still implies `WF` (table above).
2. **Two refactors of `Spec.lean` in A2,** with no change in behaviour (the differentials re-ran clean):
   - `owner` and `qRemove` name the order by id, not by structural `BEq` on `Order`, which is derived and not lawful. That fits "a handle names one order; the hash keeps ids unique".
   - The post-only test's book part is the named function `postOnlyCross`. An inline `match` elaborates to its own auxiliary matcher, which no lemma stated separately can mention.

   The C line ↔ Lean line table was updated.
3. **Theorem statement:** `∃ w, Walk.process cap b req = some w ∧ obsSpec w = obsSpec (processB cap b req)`. This follows from `Walk.process` returning `Option` (A1 deviation 2).

## Findings

1. **The continuation device moved; it did not disappear.**
   - A2 relates the walk to `doMatch` through `MatcherSpec.rest` and `rest_step`. That is the device behind the direct proof's `spec : c.mr = rest …` clause. Here it is `OW.rel` and the `rest` equations of `step_sim`/`inner_sim`.
   - What changed is where it lives. It is a statement over Lean lists only, so no store, handle or `InvM` fact is mixed into it.
   - A3 should then need no continuation clause. That is the claim A4 will measure.
2. **One walk step is one reference step,** with exactly three bookkeeping differences (the table above). No reference branch needed reordering; there is no trade reordering and no missing trade field.
3. **The trades agree as full reference `Trade` records,** element for element, not only under `tradeObs`. So do the extra fields `aggPostOnly`, `aggStpGroup`, `pasStpGroup` and `aggStpPolicy`.
4. **Cancel agrees exactly,** not only through the view, on books with unique ids, distinct prices and no empty level.
5. **The rest block's failure returns are dead on `WF` books,** now by proof (A1 Finding 5 stated this on the evidence).
6. **For `main`'s EVIDENCE.md, not changed here:**
   - `main`'s Phase 3 differential stream at capacity 20 (`genReq`, seed 7, 400 × 60) never exercises the capacity reject: 0 code-5 results, 0 pessimistic.
   - This branch's fill streams (`genFill`, seed 11, 200 × 60) do: 1,382 code-5 results at cap 20, 362 of them pessimistic.
7. **Proof engineering, for A4:**
   - `omega` ignores hypotheses whose type is `Quantity`, a `def` for `Nat` in the reference, so some arithmetic went through small `Nat` lemmas.
   - An `if` whose condition contains a `match` cannot be rewritten by a separately stated lemma, which is why `postOnlyCross` is named.

## ⚑ Questions for Ara

1. **Shared-lemma scope.** A2 imports spec-only lemmas from `Run.lean`, `Accept.lean`, `Refines.lean`, `Inner.lean`, `Rest.lean` and `Cancel.lean`, not only `SpecStep.lean` (table above). Is that acceptable, counted as shared in A4? The alternative is to re-derive them under `lean/Walk/`, roughly 250–300 lines: `pwi_cases`, `processB_after_static`, `insSpec_*`, `specOrd_of`, the `nB` normal forms.

## Next phase, first step

A3, `lean/Walk/Refine.lean`:
1. Prove `WF_of_Inv` (infrastructure).
2. Then the inner body lemma: one execution of `sideFun`'s inner body from (store, locals) related to `st` yields (store', locals') related to `innerStep st`. The relation is `bookView (absBook (view s)) = bookView st.book` (up to the empty head level being present in both), `rem = st.rem`, `emitted = st.trades.map tradeObs`, plus the two derived-local clauses.
3. It reuses `main`'s `StoreStep` and `LoopEnv` statement lemmas as infrastructure, listed at A3.

Sessions so far: A0 1, A1 1, A2 1.
