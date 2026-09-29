# Walk-spec A3b status (archived; was STATUS-W.md at 1cda4dd)

Commit: see `git log -1 -- docs/walk-spec/STATUS-W.md`   Branch: walk-spec   lake build: clean (115 jobs, no warnings in `lean/Walk/`), before and after   sorry count under lean/Walk: 0

Earlier records: `A0-INVENTORY.md`, `A2-STATUS.md`, `A3a-STATUS.md`; the A1 status is in git history at `d9e83c8`.

**Summary:**
- **`Walk.refines` is proved.** For every store satisfying `Inv` and every request, the program's run returns `Walk.process`'s result code, trades and book view, and `Inv` holds again (`WRefines`).
- **`Walk.matcher_refines` is proved as its corollary,** with `main`'s statement verbatim. `example : type_of% @Walk.matcher_refines = type_of% @MatcherAccept.matcher_refines := rfl` checks.
- `#print axioms Walk.matcher_refines` gives `propext`, `Classical.choice`, `Quot.sound`.
- **Dependency check.** The transitive closure of `Walk.matcher_refines` (computed with a small `#eval` over the environment) contains none of `main`'s:
  - loop proofs (`inner_body`, `inner_loop`, `outer_body`, `outer_loop`);
  - side and accept proofs (`side_cont`, `side_run`, `refines_accept`);
  - invariants (`IInv`, `SInv`, `OInv`, `OCtx`, `MCtx`) and their helpers (`head_facts`, `core_facts`, `sinv_*`);
  - `matcher_refines` itself.

  The only direct-route lemma it reaches is `MatcherSpec.rest_step`, used by A2's `step_sim` as approved.

## Done

| File | Lines | Contents |
|---|---|---|
| `lean/Walk/RefineOuter.lean` | 525 | `WFr` and the walk frame lemmas (`innerStep_fr` … `outerRun_fr`, `innerRun_stop`); `WO`; `w_outer_body`; `w_outer_body_trap`; `w_outer_run`/`w_outer_run_none`; `w_outer_loop` |
| `lean/Walk/Refine.lean` | 517 | view transfer (`count_of_view`, `levelsUsed_of_view`, `idOnBook_of_view`, `fr_facts`); `rest_accept`, `insSpec_views`; `w_side_cont`, `w_side_run`; `WRefines`; `w_refines_accept`; **`refines`**; **`matcher_refines`** |

### 4. Outer body and outer loop

`WO r isBuy s L ts st` is the relation at outer-iteration boundaries:
- `Inv s`, `main`'s invariant with no empty level;
- the identity clauses: `bookView`, `rem`, `stop`, trades;
- `stopX`: once `stop` is set, no contra level crosses. This is the walk's exit clause stated on the store and established by `main`'s `stopX_of_best`. The resting step's uncrossedness needs it.

The lemmas:
- **`w_outer_body`:** level fetch, the two stop tests, `qFirst`, the inner loop (A3a's `w_inner_loop` under `WR`), and the cleanup.
  - The cleanup uses `main`'s `ev_free`/`ev_nofree`, and `free_clientInv`/`free_levels_resting`/`free_restingCount`/`free_tree_length` to go from `InvM` back to `Inv`.
  - The book clause after the cleanup: `free_absSide` against the walk's `dropBest`.
- **`w_outer_body_trap`**, **`w_outer_run`/`w_outer_run_none`**, **`w_outer_loop`:** both directions, as for the inner loop.

### 5. Side function, entry, rest, result code

- **`w_side_run`:** post-only (the walk's `postOnlyCross` against the program's `poStmt`, both cases), then `w_side_cont`.
- **`w_side_cont`:**
  - `rem := qty`, then the outer loop.
  - The resting step: `main`'s `rest_run` (program), `rest_inv` (`Inv` after resting) and `rest_book` (the decoded own side) against A2's walk-side `rest_accept`.
  - The resting step's preconditions (count below capacity, the id not hashed, `rem ≤ qty`) come from the walk frame `outerRun_fr` through the view (`fr_facts`, `count_of_view`, `idOnBook_of_view`), not from extra invariant clauses.
  - Result code `ACCEPTED`.
- **`w_refines_accept`:** `main`'s entry glue (`prefix_run`, `eval_dup`, `ev_dupcheck`, `ev_capcheck`, `ev_call_side`, `order_run`) with `w_side_run` in place of `side_run`.
- **Entry rejections and cancel.** `refines` takes them from `main`'s `refines_static`, `refines_duplicate`, `refines_capacity` (`Refines.lean`) and `refines_cancel` (`Cancel.lean`), together with A2's exact agreement on those cases (`processOrder_entry`, `cancel_eq`). Those files are outside both routes' specific totals as Ara defined them (⚑1).

### 6. `matcher_refines`

From `refines` and A2's `process_agree` (with `WF_of_Inv`): the result code and trades equal `processB`'s, and the book view equal through `bookView_iff`. That is 11 lines.

### 7. Evidence re-run

- `docs/walk-spec/walk_diff.sh`: 8 configurations, 144,000 steps, D1 0, D2 0, 0 traps, 10,279 pessimistic capacity rejects.
- `MUTANT=1` (Spec.lean:196): caught by D1 (14) and D2 (14).
- `MUTANT=2` (Spec.lean:236): caught by D1 (11) and D2 (11), with 29 traps.

## A3b lemmas: mechanical or not

| Lemma | Lines | Mechanical? | Note |
|---|---|---|---|
| walk frame (`WFr`, `innerStep_rem_le`, `innerStep_stop`, `innerRun_stop`, `innerStep_fr`, `innerRun_fr`, `outerStep_fr`, `outerRun_fr`) | 130 | mechanical | walk-only, case analysis of one step |
| `WO` (definition) | 10 | — | identity + `Inv` + exit clause |
| `crosses_iff`, `side_views`, `ev_outerCond_walk` | 20 | mechanical | |
| `w_outer_body` | 150 | mechanical | `ev_*` chains and `main`'s free lemmas; the one new step is the book view after `dropBest` (`free_absSide`) |
| `w_outer_body_trap` | 81 | mechanical | inversion down to the inner loop |
| `w_outer_run`, `w_outer_run_none`, `w_outer_loop` | 92 | mechanical | induction mirroring `outerRun` |
| view transfer (`count_of_view`, `levelsUsed_of_view`, `idOnBook_of_view`, `idOnBook_sides`, `fr_facts`) | 60 | mechanical | |
| `rest_accept`, `insSpec_views` | 44 | mechanical | A2's rest lemmas and `main`'s `nL` normal forms |
| `w_side_cont` | 154 | mechanical | **one design choice:** the resting step's store preconditions come from the walk frame through the view |
| `w_side_run` | 86 | mechanical | |
| `WRefines`, `w_refines_accept`, `wrefines_of_refines`, `refines`, `matcher_refines` | 123 | mechanical | assembly |

**A3 as a whole:** apart from A3a's `book_step` (43 lines) and the `ids` clause of `WF_of_Inv`, every A3 lemma is mechanical. The prediction "the loop part is structural" holds.

## Running totals (lines; Ara's scopes)

| Route | Files | Lines |
|---|---|---|
| **Direct, route-specific** | `Inner` 996 + `Outer` 440 + `Rest` 919 + `Accept` 649 | **3,004** |
| **Walk, route-specific** | `Spec` 432 + `Basic` 335 + `EquivEntry` 444 + `EquivMatch` 680 + `Equiv` 417 + `RefineInner` 866 + `RefineOuter` 525 + `Refine` 517 | **4,216** |
| Walk, extra: `WF_of_Inv` | `WFInv` 136 | 136 |
| Walk, extra: trap direction (language inversion) | `LogicInv` 146 | 146 |

**Caveats, to be resolved in A4's attribution:**
1. **Part of the direct total is shared.** The walk route imports and reuses store- and program-side lemmas that live in the direct route's files:
   - from `Rest.lean`: `rest_run`, `rest_inv`, `rest_book` and their helpers, about 600 of its 919 lines, none mentioning the continuation;
   - from `Outer.lean`: `ev_free`, `ev_nofree`, `free_levels_resting`, `stopX_of_best`, `count_le_cap_lc`, `pos_of_ne`;
   - from `Accept.lean`: the entry glue `ev_call_side`, `dupEnvR`, and `wouldCross`/post-only evaluation;
   - from `Inner.lean`: the view helpers.

   A4 will move these into "shared" on both sides, so the route-specific comparison is like for like.
2. **The walk total includes work the direct route has no counterpart for:**
   - the walking spec itself and its fuel proof (A1, 767 lines);
   - the trap direction (loop and body traps, about 300 lines, plus `LogicInv`).
3. **The walk route's A2 (1,541 lines) is where the direct route's continuation clauses went,** as a Lean-only proof.

## Deviations from PLAN-W.md (what, why)

1. **The rejection and cancel cases use `main`'s lemmas** plus A2's exact agreement (⚑1).
2. **`WO` has no count or hash clause.** The resting step's store preconditions come from a walk-only frame lemma (`outerRun_fr`) through the view. PLAN-W did not prescribe this; it avoids re-adding the direct route's `cnt`/`hashid`/`remle` clauses.
3. **`Walk.refines` is stated as `WRefines`,** which mirrors `main`'s `Refines` with `Walk.process … = some w` in place of `specStep`. It does not use PLAN-W §3's `execStmt … = .ok` shape, because `main`'s entry point is `runEntry` and its `Refines` is stated that way.

## Findings

1. **`matcher_refines` follows from `Walk.refines` and A2 in 11 lines,** and needs none of the direct route's loop proofs or invariants (dependency check above).
2. **No continuation clause anywhere in A3.** The outer relation is identity + `Inv` + the store form of the walk's exit clause.

   Of the direct `OInv`'s 13 clauses:

   | Clause | What became of it |
   |---|---|
   | `spec`, `aggr`, `shape`, `stopT` | moved into A2 (Lean-only) |
   | `tbound` | disappeared (the emit tests coincide) |
   | `cnt`, `hashid`, `remle` | replaced by one walk-only frame lemma used through the view |
   | `inv`, `own`, `cview`, `trades`, `stopX` | remain, as `Inv`, the `bookView` identity, the trades identity and `stopX` |

3. **`Rest.lean` is mostly not route-specific.** Its resting-step lemmas carry no continuation, and the walk route reuses them unchanged. The same is true of `Outer.lean`'s free and cleanup lemmas. "Route-specific" as a file-level scope overstates the direct route's specific cost.
4. **Everything in A3b went through by unfolding and statement evaluation.** The obstacles were engineering:
   - name clashes between `Walk.tBest`/`count`/`hashFind` and the store operations;
   - `wctx` projections;
   - `rw` under `decide`;
   - `cases` on a `Prop`.

## ⚑ Questions for Ara

1. **Scope of the rejection and cancel cases.** `Walk.refines` takes those four cases from `main`'s `refines_static`/`refines_duplicate`/`refines_capacity`/`refines_cancel`, since `Walk.process` equals `processB` exactly there (A2). That matches your A4 scope, since `Refines.lean`/`Cancel.lean` are outside both route-specific totals. Is it acceptable?
   - The alternative is a walk-native proof of those cases.
   - For cancel, that would restate `Cancel.lean`'s store-view argument against `Walk.cancel`, which equals `cancelOrder` exactly. So it adds no new content, at a cost of roughly 300–500 lines.

## Next

A4: `docs/walk-spec/RESULT-W.md`. It will contain:
- the lemma-by-lemma table, with each lemma's lines split into store-side / spec-relation / glue;
- totals per route and overall;
- which store operations recur in the most branches (popping one resting order is three contract calls);
- what was mechanical and what needed thought (the classification above);
- where the difficulty moved;
- `walk_oracle` as an option;
- the recommendation.

Sessions: A0 1, A1 1, A2 1, A3a 1, A3b 1.
