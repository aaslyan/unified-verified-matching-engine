# Walk-spec RESULT (A4)

Branch `walk-spec`. Baseline `A0-INVENTORY.md`. Theorems: `Walk.process_obs_eq` / `Walk.process_agree` (A2), `Walk.refines` (A3), `Walk.matcher_refines` (A3; `main`'s statement, checked `rfl` against `MatcherAccept.matcher_refines`). Axioms: `propext`, `Classical.choice`, `Quot.sound`. `sorry`: 0. Evidence: `docs/walk-spec/walk_diff.sh` 144,000 steps, D1 = D2 = 0, MUTANT=1|2 caught.

Line counts are physical lines. "Declaration lines" = lines inside a declaration's range (Lean's `findDeclarationRanges?`); "with comments" additionally assigns each file's header/comment lines to its buckets in proportion. Data: `#eval` over the environment (closure of `getUsedConstants`); scripts in `docs/walk-spec/a4/`.

## 1. Dependency closure of `Walk.matcher_refines` (the independence statement)

Named declarations outside `lean/Walk/` in the closure, by module:

| Group | Module | Declarations |
|---|---|---|
| Reference spec | `MatchingEngine.Basic` | 59 |
| | `MatchingEngine.Order` | 34 |
| | `MatchingEngine.Book` | 25 |
| | `MatchingEngine.Process` | 20 |
| | `MatchingEngine.Theorems` | 15 |
| | `MatchingEngine.Match` | 10 |
| | `MatchingEngine.Cancel` | 3 |
| | `MatchingEngine.STP` | 2 |
| Bridge | `Bridge.EngineDbApi` | 161 |
| | `Bridge.EngineDbAbs` | 109 |
| | `Bridge.ProcessB` | 34 |
| | `Bridge.EngineDbApiLaws` | 17 |
| Matcher infrastructure | `Matcher.Lang` | 193 |
| | `Matcher.LoopEnv` | 86 |
| | `Matcher.Logic` | 60 |
| | `Matcher.StoreStep` | 54 |
| | `Matcher.Program` | 35 |
| | `Matcher.SpecStep` | 48 (spec-only; approved A0 ⚑4) |
| | `Matcher.Run` | 15 (`nB`/`nL`/`nO` normal forms, `pwi_cases`, `bookView_iff`, `insertDesc_nL`/`insertAsc_nL`) |
| | `Matcher.Refines` | 74 (entry evaluation, `Inv`, `Refines`, request-only checks, `refines_static`/`_duplicate`/`_capacity`) |
| | `Matcher.Cancel` | 44 (cancel store view, `refines_cancel`) |
| Direct-route files, non-continuation lemmas | `Matcher.Rest` | 39: `insSpec*`, `rest_prefix`, `rest_run`, `rest_inv`, `rest_book`, `RestView`, `join_*`, `alloc_*`, `newLevel_clientInvM`, `ev_*` of the rest block |
| | `Matcher.Accept` | 37: `SpecOrd`, `specOrd_of`, `Static`, `static_of`, `sideOf_isBuy`, `term_bids_asks`, `restOrd`, `dispose_rest`/`_norest`, `ev_poCond_*`, `ev_po_skip`, `wouldCross_o1`, `dupEnvR`, `lookup_side`, `ev_call_side` |
| | `Matcher.Inner` | 23: `IncShape` (+ accessors), `canMatch_shape`, `head_decomp`, `RowView`, `rowView_of`, `view_update`, `ordV_congr`, `qNext_head`, `nextIn_head`, `dropDb_setRem` |
| | `Matcher.Outer` | 8: `freeS`, `ev_free`, `ev_nofree`, `stopX_of_best`, `count_le_cap_lc`, `ownT_ne`, `free_levels_resting`, `pos_of_ne` |

Direct-route lemmas reached that bear the continuation or prove a refinement case: `MatcherSpec.rest_step` (via A2 `step_sim`), `MatcherRefines.refines_static`, `refines_duplicate`, `refines_capacity`, `MatcherCancel.refines_cancel`.

Not reached (checked by name): `inner_body`, `inner_loop`, `inner_run`, `inner_cancelNew`, `inner_cancelOld`, `inner_dec`, `inner_fill`, `head_facts`, `core_facts`, `sinv_drop`, `sinv_setRem`, `IInv`, `SInv`, `OCtx`, `outer_body`, `outer_run`, `outer_loop`, `OInv`, `MCtx`, `side_cont`, `side_run`, `refines_accept`, `MatcherAccept.matcher_refines`.

**Independence claim.** `Walk.matcher_refines` is independent of `main`'s proof on the matching path (inner loop, outer loop, resting step, result code of an order accepted by the entry checks). It shares with `main`: the entry rejections (`refines_static`, `refines_duplicate`, `refines_capacity`), cancel (`refines_cancel`), `MatcherSpec.rest_step` (through `step_sim`), and the infrastructure listed above.

## 2. Re-attribution

Rules, applied to both routes:

| Bucket | Rule |
|---|---|
| shared | a declaration reached from both `MatcherAccept.matcher_refines` and `Walk.matcher_refines` |
| direct-specific | a declaration in `Inner`/`Outer`/`Rest`/`Accept` reached from `MatcherAccept.matcher_refines` only. Every such declaration carries or consumes the continuation invariant except 36 lines (`view_update_st` 6, `boundVal_capPlus1` 4, `map_levelView_cons` 5, `not_mem_other` 3, `MatcherAccept.matcher_refines` 18) |
| walk-specific | a declaration in `Spec`/`Basic`/`Equiv*`/`Refine*`/`WFInv`/`LogicInv` reached from `Walk.matcher_refines`, minus extra |
| extra | proved by one route only, with no counterpart on the other: `Spec.lean` (the spec artifact), `Basic.lean` (its fuel proof and sanity lemmas), the trap direction (`LogicInv.lean`, `seq_through`, `w_inner_body_trap`, `w_inner_run_none`, `w_outer_body_trap`, `w_outer_run_none`) |
| unused | in the files, reached from neither theorem |

Totals before (file scopes as defined for the running totals):

| Route | Files | Lines |
|---|---|---|
| Direct | `Inner`+`Outer`+`Rest`+`Accept` | 3,004 |
| Walk | `Spec`+`Basic`+`Equiv*`+`Refine*` (+ `WFInv`, `LogicInv`) | 4,216 (4,498) |

Totals after:

| Bucket | Declaration lines | With comments |
|---|---|---|
| Direct-specific | 1,480 | 1,703 |
| Shared, located in the direct files | 1,113 | 1,277 |
| Direct, unused | 20 | 24 |
| Walk-specific | 2,901 | 3,320 |
| — of which A2 (walk ≡ `processB`) | 1,319 | |
| — of which A3 (program refines walk) + `WF_of_Inv` | 1,582 | |
| Walk, extra | 871 | 1,168 |
| Walk, unused | 9 | 10 |

Route-specific comparison: direct-specific **1,480** (1,703) vs walk-specific **2,901** (3,320). The refinement step alone: direct-specific 1,480 vs walk A3 1,582 (incl. `WF_of_Inv` 104). The walk route's additional specific cost is A2 (1,319).

## 3. Per-lemma tables

Three-way split, rule applied line by line to both routes (keyword rule; a line goes to the first matching class):
spec-relation — mentions the reference or walk state or a view relating store to it (`rest`, `rest_step`, `term`, `mr`, `spec`, `inc`, `contra`, `strades`, `step_*`, `AtHead`, `IncShape`, `aggr`, `drop1`, `bookView`, `levelView`, `orderView`, `absSide`, `absLevel`, `restSide`, `book_step`, `wr_split`, `view_drop`, `view_setRem`, `sideL`, `innerStep`, `outerStep`, `innerRun`, `outerRun`, `mkTrade`, `restOrder`, `insSpec`, `postOnlyCode`, `wouldCross`, walk-state hypotheses);
store-side — mentions the store (`Inv`, `InvM`, `count`, `levelsUsed`, `Frame`, `dropDb`, `setRemDb`, `freeDb`, `dropS`, `writeOrder`, `WF`, `queue`, `hash`, `restingCount`, `ClientInv`, `liveO`/`liveL`, `readOrder`/`readLevel`, `tree`, `levelPrice`, `sinv_*`, `invM_*`, `core_facts`, `wcore`, `free_*`, `rest_run`/`rest_inv`/`rest_book`);
glue — everything else (statement evaluation `Eval`/`ev_*`/`lsimp`, dispatch, assembly, structure).

Class: "content" = a statement that had to be invented (an invariant, a measure, an equivalence); "mechanical" = goes through by unfolding and statement evaluation; "not mechanical" = a proof that needed an argument beyond that.

Split totals:

| Bucket | Lines | store | spec-rel | glue |
|---|---|---|---|---|
| Direct-specific | 1,482 | 311 | 460 | 711 |
| Walk-specific A2 | 1,319 | 79 | 370 | 870 |
| Walk-specific A3 + `WF_of_Inv` | 1,582 | 345 | 393 | 844 |
| Walk extra | 871 | 38 | 205 | 628 |
| Shared (in direct files) | 1,113 | 310 | 104 | 699 |

Not mechanical, named: direct — `IInv`, `SInv`, `OCtx`/`OCtx.Ok`, `HeadFacts`, `imeasure`, `OInv`, `MCtx`/`MCtx.Ok`, `omeasure` (the invented invariant and measures; every direct loop lemma is mechanical given them). Walk — all of A2 (content by nature: `step_sim`, `inner_sim`, `OW`/`outerStep_OW`/`outer_sim`, `walkRemove_eq`, `cancel_eq`, `processOrder_entry`, `sideProc_agree` and their helpers); A3 `book_step`; the unique-ids clause of `WF_of_Inv`; A1 `innerRun_ok`/`outerRun_ok`/`run_fuel_sufficient` (the potential argument, extra).

### Direct route: direct-specific lemmas (used by `main`'s `matcher_refines`, not by the walk route)

| File | Lemma | Lines | store | spec-rel | glue | Class |
|---|---|---|---|---|---|---|
| Accept | `mr_rest` | 19 | 0 | 14 | 5 | mechanical given the invariant |
| Accept | `book_norest` | 12 | 0 | 6 | 6 | mechanical given the invariant |
| Accept | `book_rest` | 33 | 0 | 19 | 14 | mechanical given the invariant |
| Accept | `restOrd_view` | 15 | 0 | 8 | 7 | mechanical given the invariant |
| Accept | `wouldCross_iff` | 30 | 5 | 11 | 14 | mechanical given the invariant |
| Accept | `side_cont` | 124 | 16 | 32 | 76 | mechanical given the invariant |
| Accept | `side_run` | 94 | 14 | 19 | 61 | mechanical given the invariant |
| Accept | `refines_accept` | 51 | 2 | 5 | 44 | mechanical given the invariant |
| Accept | `matcher_refines` | 18 | 4 | 0 | 14 | mechanical given the invariant |
| Inner | `ReqOk` | 6 | 0 | 0 | 6 | mechanical given the invariant |
| Inner | `RowView.vis` | 1 | 0 | 0 | 1 | mechanical given the invariant |
| Inner | `RowView.disp` | 1 | 0 | 0 | 1 | mechanical given the invariant |
| Inner | `view_update_st` | 6 | 0 | 5 | 1 | mechanical given the invariant |
| Inner | `conflict_iff` | 22 | 0 | 4 | 18 | mechanical given the invariant |
| Inner | `policy_of` | 9 | 0 | 6 | 3 | mechanical given the invariant |
| Inner | `OCtx` | 12 | 0 | 2 | 10 | content: fixed data incl. the final result `mr` |
| Inner | `OCtx.t` | 1 | 0 | 0 | 1 | mechanical given the invariant |
| Inner | `OCtx.Ok` | 10 | 4 | 3 | 3 | content |
| Inner | `SInv` | 9 | 4 | 4 | 1 | content: store part of the invariant, tied to the reference contra list |
| Inner | `IInv` | 13 | 2 | 7 | 4 | content: the continuation invariant |
| Inner | `imeasure` | 3 | 1 | 0 | 2 | content: loop measure |
| Inner | `SInv.mem` | 3 | 1 | 2 | 0 | mechanical given the invariant |
| Inner | `SInv.liveL` | 3 | 1 | 2 | 0 | mechanical given the invariant |
| Inner | `sinv_drop` | 52 | 19 | 24 | 9 | mechanical given the invariant |
| Inner | `sinv_setRem` | 55 | 21 | 20 | 14 | mechanical given the invariant |
| Inner | `HeadFacts` | 24 | 7 | 9 | 8 | content: head facts incl. `AtHead` and `aggr` |
| Inner | `head_facts` | 40 | 6 | 24 | 10 | mechanical given the invariant |
| Inner | `IStep` | 5 | 0 | 2 | 3 | mechanical given the invariant |
| Inner | `conflict_of` | 8 | 0 | 6 | 2 | mechanical given the invariant |
| Inner | `inner_cancelNew` | 20 | 0 | 9 | 11 | mechanical given the invariant |
| Inner | `inner_cancelOld` | 75 | 14 | 17 | 44 | mechanical given the invariant |
| Inner | `Core` | 27 | 19 | 5 | 3 | mechanical given the invariant |
| Inner | `core_facts` | 48 | 26 | 8 | 14 | mechanical given the invariant |
| Inner | `decInc_aggr` | 7 | 0 | 5 | 2 | mechanical given the invariant |
| Inner | `inner_dec` | 120 | 38 | 29 | 53 | mechanical given the invariant |
| Inner | `count_pos_of_head` | 11 | 4 | 4 | 3 | mechanical given the invariant |
| Inner | `inner_fill` | 136 | 46 | 33 | 57 | mechanical given the invariant |
| Inner | `inner_body` | 17 | 2 | 3 | 12 | mechanical given the invariant |
| Inner | `inner_run` | 36 | 4 | 11 | 21 | mechanical given the invariant |
| Inner | `boundVal_capPlus1` | 4 | 0 | 0 | 4 | mechanical given the invariant |
| Inner | `inner_loop` | 23 | 2 | 8 | 13 | mechanical given the invariant |
| Outer | `MCtx` | 9 | 0 | 1 | 8 | content: fixed data incl. `mr` |
| Outer | `MCtx.t` | 1 | 0 | 0 | 1 | mechanical given the invariant |
| Outer | `MCtx.Ok` | 4 | 0 | 0 | 4 | content |
| Outer | `OInv` | 17 | 5 | 9 | 3 | content: the continuation invariant |
| Outer | `omeasure` | 2 | 1 | 0 | 1 | content: loop measure |
| Outer | `notDone_of` | 11 | 0 | 7 | 4 | mechanical given the invariant |
| Outer | `done_of` | 7 | 0 | 4 | 3 | mechanical given the invariant |
| Outer | `canMatch_iff` | 9 | 0 | 1 | 8 | mechanical given the invariant |
| Outer | `map_levelView_cons` | 5 | 0 | 1 | 4 | mechanical given the invariant |
| Outer | `oc` | 4 | 0 | 3 | 1 | mechanical given the invariant |
| Outer | `not_mem_other` | 3 | 3 | 0 | 0 | mechanical given the invariant |
| Outer | `OStep` | 4 | 0 | 2 | 2 | mechanical given the invariant |
| Outer | `outer_body` | 144 | 39 | 39 | 66 | mechanical given the invariant |
| Outer | `outer_run` | 33 | 0 | 14 | 19 | mechanical given the invariant |
| Outer | `outer_loop` | 26 | 1 | 13 | 12 | mechanical given the invariant |
| | **total** | **1482** | **311** | **460** | **711** | |

### Walk route: walk-specific lemmas

| File | Lemma | Lines | store | spec-rel | glue | Class |
|---|---|---|---|---|---|---|
| Equiv | `nB_eq_of_sides` | 6 | 0 | 4 | 2 | A2 content |
| Equiv | `allIds` | 8 | 0 | 4 | 4 | A2 content |
| Equiv | `count_sides` | 5 | 0 | 1 | 4 | A2 content |
| Equiv | `levelsUsed_sides` | 4 | 0 | 3 | 1 | A2 content |
| Equiv | `hashFind_none_of` | 13 | 0 | 1 | 12 | A2 content |
| Equiv | `length_le_ids` | 2 | 0 | 0 | 2 | A2 content |
| Equiv | `modAt_eq_map` | 18 | 0 | 4 | 14 | A2 content |
| Equiv | `modAt_insLevel` | 12 | 0 | 0 | 12 | A2 content |
| Equiv | `nO_restOrder` | 13 | 0 | 5 | 8 | A2 content |
| Equiv | `sideL_insertOrder` | 9 | 0 | 8 | 1 | A2 content |
| Equiv | `rest_found` | 9 | 1 | 4 | 4 | A2 content |
| Equiv | `rest_fresh` | 10 | 1 | 6 | 3 | A2 content |
| Equiv | `rest_none` | 3 | 0 | 2 | 1 | A2 content |
| Equiv | `CO_of` | 10 | 0 | 0 | 10 | A2 content |
| Equiv | `mr_eq` | 12 | 0 | 8 | 4 | A2 content |
| Equiv | `postOnly_iff` | 17 | 0 | 5 | 12 | A2 content |
| Equiv | `sideProc_agree` | 190 | 27 | 55 | 108 | A2 content |
| Equiv | `process_agree` | 14 | 8 | 0 | 6 | A2 content |
| EquivEntry | `WF` | 11 | 2 | 3 | 6 | A2 content |
| EquivEntry | `find_isSome_any` | 5 | 0 | 0 | 5 | A2 content |
| EquivEntry | `hashFind_isSome` | 2 | 0 | 0 | 2 | A2 content |
| EquivEntry | `eq_of_nodup_ids` | 12 | 0 | 0 | 12 | A2 content |
| EquivEntry | `count_eq_bookSize` | 2 | 0 | 2 | 0 | A2 content |
| EquivEntry | `allBookOrders_sides` | 2 | 0 | 1 | 1 | A2 content |
| EquivEntry | `processOrder_eq` | 30 | 1 | 0 | 29 | A2 content |
| EquivEntry | `Agree` | 3 | 0 | 0 | 3 | A2 content |
| EquivEntry | `Agree.refl` | 1 | 0 | 0 | 1 | A2 content |
| EquivEntry | `processOrder_entry` | 34 | 6 | 6 | 22 | A2 content |
| EquivEntry | `walkRemove` | 5 | 0 | 0 | 5 | A2 content |
| EquivEntry | `eraseP_eq_filter` | 17 | 0 | 0 | 17 | A2 content |
| EquivEntry | `removeLevelOrder_keep` | 14 | 0 | 0 | 14 | A2 content |
| EquivEntry | `modAt_append_cons` | 9 | 0 | 0 | 9 | A2 content |
| EquivEntry | `walkRemove_eq` | 69 | 0 | 2 | 67 | A2 content |
| EquivEntry | `none_of_isSome_false` | 2 | 0 | 0 | 2 | A2 content |
| EquivEntry | `hasId` | 2 | 0 | 0 | 2 | A2 content |
| EquivEntry | `srch_fst` | 34 | 0 | 0 | 34 | A2 content |
| EquivEntry | `find_some_of_hasId` | 10 | 0 | 0 | 10 | A2 content |
| EquivEntry | `find_none_of_hasId` | 6 | 0 | 0 | 6 | A2 content |
| EquivEntry | `flat_find` | 5 | 0 | 0 | 5 | A2 content |
| EquivEntry | `sideL_setSideL_twice` | 2 | 0 | 0 | 2 | A2 content |
| EquivEntry | `cancel_side` | 9 | 0 | 3 | 6 | A2 content |
| EquivEntry | `nodup_side` | 6 | 0 | 1 | 5 | A2 content |
| EquivEntry | `mem_side_of_find` | 7 | 0 | 0 | 7 | A2 content |
| EquivEntry | `cancel_eq` | 84 | 3 | 4 | 77 | A2 content |
| EquivMatch | `done` | 2 | 0 | 1 | 1 | A2 content |
| EquivMatch | `Good` | 3 | 0 | 0 | 3 | A2 content |
| EquivMatch | `normC` | 4 | 0 | 0 | 4 | A2 content |
| EquivMatch | `normC_cons_ne` | 2 | 0 | 0 | 2 | A2 content |
| EquivMatch | `normC_cons_nil` | 2 | 0 | 0 | 2 | A2 content |
| EquivMatch | `CO` | 10 | 0 | 0 | 10 | A2 content |
| EquivMatch | `IR` | 5 | 0 | 4 | 1 | A2 content |
| EquivMatch | `IR.notDone` | 9 | 0 | 6 | 3 | A2 content |
| EquivMatch | `u64_toNat_ne_zero` | 2 | 0 | 0 | 2 | A2 content |
| EquivMatch | `conflict_iff` | 20 | 0 | 3 | 17 | A2 content |
| EquivMatch | `policy_of` | 10 | 0 | 6 | 4 | A2 content |
| EquivMatch | `canMatch_iff` | 9 | 0 | 4 | 5 | A2 content |
| EquivMatch | `mkTrade_eq` | 8 | 0 | 5 | 3 | A2 content |
| EquivMatch | `Ctx.own_ne` | 2 | 0 | 2 | 0 | A2 content |
| EquivMatch | `sideL_setSideL_ne` | 3 | 0 | 1 | 2 | A2 content |
| EquivMatch | `stops_setSideL` | 2 | 0 | 0 | 2 | A2 content |
| EquivMatch | `own_frame` | 2 | 0 | 1 | 1 | A2 content |
| EquivMatch | `ids` | 2 | 0 | 0 | 2 | A2 content |
| EquivMatch | `step_sim` | 174 | 5 | 80 | 89 | A2 content |
| EquivMatch | `ids_cons` | 2 | 0 | 0 | 2 | A2 content |
| EquivMatch | `sideCount_eq_ids` | 4 | 0 | 0 | 4 | A2 content |
| EquivMatch | `innerStep_frame` | 60 | 1 | 24 | 35 | A2 content |
| EquivMatch | `inner_sim` | 80 | 10 | 29 | 41 | A2 content |
| EquivMatch | `NonE` | 1 | 0 | 0 | 1 | A2 content |
| EquivMatch | `GoodL` | 1 | 0 | 0 | 1 | A2 content |
| EquivMatch | `outerRun_final` | 14 | 0 | 6 | 8 | A2 content |
| EquivMatch | `OW` | 16 | 0 | 10 | 6 | A2 content |
| EquivMatch | `IR.sameRem` | 2 | 0 | 2 | 0 | A2 content |
| EquivMatch | `ids_sub_of_head` | 4 | 0 | 0 | 4 | A2 content |
| EquivMatch | `outerStep_OW` | 102 | 10 | 47 | 45 | A2 content |
| EquivMatch | `outer_sim` | 24 | 4 | 7 | 13 | A2 content |
| Refine | `count_of_view` | 11 | 1 | 6 | 4 | mechanical |
| Refine | `levelsUsed_of_view` | 6 | 2 | 4 | 0 | mechanical |
| Refine | `idOnBook_of_view` | 13 | 0 | 6 | 7 | mechanical |
| Refine | `idOnBook_sides` | 14 | 0 | 1 | 13 | mechanical |
| Refine | `fr_facts` | 11 | 0 | 2 | 9 | mechanical |
| Refine | `rest_accept` | 33 | 2 | 11 | 20 | mechanical |
| Refine | `insSpec_views` | 9 | 0 | 5 | 4 | mechanical |
| Refine | `w_side_cont` | 154 | 19 | 30 | 105 | mechanical |
| Refine | `w_side_run` | 86 | 21 | 18 | 47 | mechanical |
| Refine | `WRefines` | 6 | 1 | 1 | 4 | mechanical |
| Refine | `w_refines_accept` | 42 | 3 | 3 | 36 | mechanical |
| Refine | `wrefines_of_refines` | 6 | 0 | 0 | 6 | mechanical |
| Refine | `refines` | 54 | 10 | 2 | 42 | mechanical |
| Refine | `matcher_refines` | 12 | 3 | 2 | 7 | mechanical |
| RefineInner | `wctx` | 3 | 0 | 0 | 3 | mechanical |
| RefineInner | `wctx_contra` | 1 | 0 | 1 | 0 | mechanical |
| RefineInner | `WR` | 13 | 5 | 1 | 7 | mechanical |
| RefineInner | `bookView_sides` | 6 | 0 | 5 | 1 | mechanical |
| RefineInner | `sideL_absBook` | 2 | 0 | 1 | 1 | mechanical |
| RefineInner | `book_step` | 45 | 12 | 13 | 20 | not mechanical (A3a) |
| RefineInner | `wr_split` | 22 | 1 | 9 | 12 | mechanical |
| RefineInner | `WHead` | 21 | 7 | 6 | 8 | mechanical |
| RefineInner | `whead` | 19 | 10 | 4 | 5 | mechanical |
| RefineInner | `acct_iff` | 16 | 0 | 5 | 11 | mechanical |
| RefineInner | `invM_drop` | 15 | 12 | 0 | 3 | mechanical |
| RefineInner | `invM_setRem` | 21 | 15 | 0 | 6 | mechanical |
| RefineInner | `best_frame` | 6 | 5 | 0 | 1 | mechanical |
| RefineInner | `view_drop` | 15 | 3 | 6 | 6 | mechanical |
| RefineInner | `view_setRem` | 22 | 5 | 10 | 7 | mechanical |
| RefineInner | `WCore` | 25 | 21 | 0 | 4 | mechanical |
| RefineInner | `wcore` | 32 | 22 | 0 | 10 | mechanical |
| RefineInner | `ev_innerCond_walk` | 24 | 5 | 5 | 14 | mechanical |
| RefineInner | `w_inner_body` | 305 | 109 | 68 | 128 | mechanical |
| RefineInner | `w_inner_run` | 39 | 0 | 7 | 32 | mechanical |
| RefineInner | `boundVal_capPlus1'` | 4 | 0 | 0 | 4 | mechanical |
| RefineInner | `w_inner_loop` | 17 | 0 | 3 | 14 | mechanical |
| RefineOuter | `WFr` | 7 | 0 | 4 | 3 | mechanical |
| RefineOuter | `WFr.refl` | 2 | 0 | 0 | 2 | mechanical |
| RefineOuter | `WFr.trans` | 2 | 0 | 0 | 2 | mechanical |
| RefineOuter | `innerStep_rem_le` | 16 | 0 | 15 | 1 | mechanical |
| RefineOuter | `innerStep_stop` | 16 | 0 | 15 | 1 | mechanical |
| RefineOuter | `innerRun_stop` | 12 | 0 | 6 | 6 | mechanical |
| RefineOuter | `innerStep_fr` | 9 | 0 | 6 | 3 | mechanical |
| RefineOuter | `innerRun_fr` | 11 | 0 | 6 | 5 | mechanical |
| RefineOuter | `outerStep_fr` | 36 | 0 | 19 | 17 | mechanical |
| RefineOuter | `outerRun_fr` | 11 | 0 | 6 | 5 | mechanical |
| RefineOuter | `WO` | 10 | 2 | 1 | 7 | mechanical |
| RefineOuter | `crosses_iff` | 4 | 0 | 3 | 1 | mechanical |
| RefineOuter | `side_views` | 3 | 0 | 2 | 1 | mechanical |
| RefineOuter | `w_outer_body` | 151 | 27 | 55 | 69 | mechanical |
| RefineOuter | `ev_outerCond_walk` | 8 | 0 | 2 | 6 | mechanical |
| RefineOuter | `w_outer_run` | 36 | 0 | 7 | 29 | mechanical |
| RefineOuter | `w_outer_loop` | 14 | 0 | 2 | 12 | mechanical |
| WFInv | `nodup_map_of_inj` | 11 | 0 | 0 | 11 | mechanical |
| WFInv | `nodup_flatMap_of` | 15 | 3 | 0 | 12 | mechanical |
| WFInv | `absQueue_ids` | 5 | 0 | 3 | 2 | mechanical |
| WFInv | `absSide_ids_perm` | 13 | 1 | 4 | 8 | mechanical |
| WFInv | `WF_of_Inv` | 60 | 18 | 2 | 40 | not mechanical: the unique-ids clause |
| | **total** | **2901** | **424** | **763** | **1714** | |

### Walk route: extra (spec artifact, its fuel proof, the trap direction)

| File | Lemma | Lines | store | spec-rel | glue | Class |
|---|---|---|---|---|---|---|
| Basic | `sideL_setSideL` | 2 | 0 | 1 | 1 | mechanical |
| Basic | `modHead_cons` | 2 | 0 | 0 | 2 | mechanical |
| Basic | `sideL_popHead` | 3 | 0 | 1 | 2 | mechanical |
| Basic | `sideL_setHeadRem` | 6 | 0 | 2 | 4 | mechanical |
| Basic | `sideL_dropBest` | 3 | 0 | 1 | 2 | mechanical |
| Basic | `tBest_eq` | 1 | 0 | 1 | 0 | mechanical |
| Basic | `sideCount` | 2 | 0 | 0 | 2 | mechanical |
| Basic | `contraCount` | 2 | 0 | 1 | 1 | mechanical |
| Basic | `pot` | 2 | 0 | 0 | 2 | mechanical |
| Basic | `sideCount_cons` | 3 | 0 | 0 | 3 | mechanical |
| Basic | `rem_zero_of_prem_pos` | 2 | 0 | 0 | 2 | mechanical |
| Basic | `innerStep_shape` | 39 | 0 | 18 | 21 | mechanical |
| Basic | `innerStep_isSome` | 15 | 0 | 3 | 12 | mechanical |
| Basic | `innerStep_progress` | 17 | 0 | 7 | 10 | mechanical |
| Basic | `innerRun_exit` | 3 | 0 | 3 | 0 | mechanical |
| Basic | `outerRun_exit` | 3 | 0 | 3 | 0 | mechanical |
| Basic | `innerRun_stable` | 17 | 0 | 6 | 11 | mechanical |
| Basic | `outerRun_stable` | 17 | 0 | 6 | 11 | mechanical |
| Basic | `innerRun_ok` | 47 | 0 | 14 | 33 | not mechanical: potential argument |
| Basic | `length_le_sideCount` | 8 | 0 | 0 | 8 | mechanical |
| Basic | `outerRun_ok` | 44 | 0 | 13 | 31 | not mechanical: potential argument |
| Basic | `sideCount_le_count` | 7 | 0 | 2 | 5 | mechanical |
| Basic | `sideProc_isSome` | 9 | 0 | 1 | 8 | mechanical |
| Basic | `run_fuel_sufficient` | 23 | 1 | 6 | 16 | not mechanical: potential argument |
| LogicInv | `loopStep_cases` | 14 | 0 | 0 | 14 | mechanical (trap direction) |
| LogicInv | `loopRun_of_fold` | 26 | 0 | 0 | 26 | mechanical (trap direction) |
| LogicInv | `loopRun_of_eval` | 11 | 0 | 0 | 11 | mechanical (trap direction) |
| LogicInv | `Eval.seq_inv` | 16 | 0 | 0 | 16 | mechanical (trap direction) |
| LogicInv | `Eval.ite_inv` | 19 | 0 | 0 | 19 | mechanical (trap direction) |
| LogicInv | `Eval.emit_inv` | 31 | 0 | 0 | 31 | mechanical (trap direction) |
| RefineInner | `seq_through` | 5 | 2 | 0 | 3 | mechanical (trap direction) |
| RefineInner | `w_inner_body_trap` | 61 | 15 | 15 | 31 | mechanical (trap direction) |
| RefineInner | `w_inner_run_none` | 42 | 0 | 7 | 35 | mechanical (trap direction) |
| RefineOuter | `w_outer_body_trap` | 82 | 13 | 30 | 39 | mechanical (trap direction) |
| RefineOuter | `w_outer_run_none` | 39 | 0 | 7 | 32 | mechanical (trap direction) |
| Spec | `sideL` | 4 | 0 | 1 | 3 | spec artifact (definition) |
| Spec | `setSideL` | 3 | 0 | 0 | 3 | spec artifact (definition) |
| Spec | `modHead` | 4 | 0 | 0 | 4 | spec artifact (definition) |
| Spec | `modAt` | 4 | 0 | 0 | 4 | spec artifact (definition) |
| Spec | `tBest` | 2 | 0 | 1 | 1 | spec artifact (definition) |
| Spec | `qFirst` | 2 | 0 | 0 | 2 | spec artifact (definition) |
| Spec | `levelCount` | 2 | 0 | 0 | 2 | spec artifact (definition) |
| Spec | `getAccount` | 3 | 0 | 0 | 3 | spec artifact (definition) |
| Spec | `setHeadRem` | 8 | 0 | 1 | 7 | spec artifact (definition) |
| Spec | `popHead` | 6 | 2 | 1 | 3 | spec artifact (definition) |
| Spec | `dropBest` | 3 | 0 | 1 | 2 | spec artifact (definition) |
| Spec | `count` | 2 | 1 | 0 | 1 | spec artifact (definition) |
| Spec | `levelsUsed` | 2 | 1 | 0 | 1 | spec artifact (definition) |
| Spec | `hashFind` | 3 | 0 | 0 | 3 | spec artifact (definition) |
| Spec | `owner` | 7 | 1 | 0 | 6 | spec artifact (definition) |
| Spec | `qRemove` | 3 | 0 | 1 | 2 | spec artifact (definition) |
| Spec | `qRemoveTail` | 3 | 0 | 1 | 2 | spec artifact (definition) |
| Spec | `tRemove` | 3 | 0 | 1 | 2 | spec artifact (definition) |
| Spec | `tFind` | 3 | 0 | 1 | 2 | spec artifact (definition) |
| Spec | `tInsertNew` | 4 | 1 | 1 | 2 | spec artifact (definition) |
| Spec | `qInsertTail` | 3 | 0 | 1 | 2 | spec artifact (definition) |
| Spec | `Ctx` | 5 | 0 | 0 | 5 | spec artifact (definition) |
| Spec | `Ctx.contra` | 1 | 0 | 1 | 0 | spec artifact (definition) |
| Spec | `Ctx.own` | 1 | 0 | 0 | 1 | spec artifact (definition) |
| Spec | `Ctx.crosses` | 4 | 0 | 1 | 3 | spec artifact (definition) |
| Spec | `Ctx.bound` | 3 | 0 | 0 | 3 | spec artifact (definition) |
| Spec | `State` | 6 | 0 | 0 | 6 | spec artifact (definition) |
| Spec | `mkTrade` | 10 | 0 | 1 | 9 | spec artifact (definition) |
| Spec | `innerTest` | 3 | 0 | 2 | 1 | spec artifact (definition) |
| Spec | `innerStep` | 32 | 0 | 10 | 22 | spec artifact (definition) |
| Spec | `innerRun` | 4 | 0 | 3 | 1 | spec artifact (definition) |
| Spec | `outerTest` | 2 | 0 | 1 | 1 | spec artifact (definition) |
| Spec | `outerStep` | 15 | 0 | 6 | 9 | spec artifact (definition) |
| Spec | `outerRun` | 4 | 0 | 3 | 1 | spec artifact (definition) |
| Spec | `restOrder` | 10 | 0 | 1 | 9 | spec artifact (definition) |
| Spec | `rest` | 24 | 0 | 10 | 14 | spec artifact (definition) |
| Spec | `postOnlyCross` | 6 | 0 | 4 | 2 | spec artifact (definition) |
| Spec | `sideProc` | 9 | 0 | 3 | 6 | spec artifact (definition) |
| Spec | `reject` | 2 | 0 | 0 | 2 | spec artifact (definition) |
| Spec | `processOrder` | 14 | 1 | 0 | 13 | spec artifact (definition) |
| Spec | `cancel` | 15 | 0 | 0 | 15 | spec artifact (definition) |
| Spec | `process` | 4 | 0 | 0 | 4 | spec artifact (definition) |
| | **total** | **871** | **38** | **205** | **628** | |

### Shared lemmas inside the direct route's files (used by both routes), per file

| File | Declarations | Lines | store | spec-rel | glue |
|---|---|---|---|---|---|
| Inner | 19 | 74 | 12 | 27 | 35 |
| Outer | 8 | 95 | 38 | 0 | 57 |
| Rest | 39 | 802 | 259 | 56 | 487 |
| Accept | 16 | 142 | 1 | 21 | 120 |
| **total** | | **1113** | **310** | **104** | **699** |

## 4. The outer invariant's clauses

`OInv` (direct, `Outer.lean:103`), 13 clauses:

| Clause | Direct: established/maintained by | Walk: becomes | Walk lemma |
|---|---|---|---|
| `spec : mr = rest inc own contra strades tm` | `outer_body`, `inner_*` via `rest_step` | moved to A2 | `OW.rel`, `step_sim`, `inner_sim`, `outerStep_OW` |
| `aggr : rem = (inc cancelled ? 0 : inc.remainingQty)` | `inner_*` | moved to A2 | `IR` (`zero`, `pos`) |
| `shape : IncShape o1 inc` | `inner_*` | moved to A2 | `IR.shape` |
| `stopT : stop → mr = term …` | `outer_body` (`rest_empty`, `rest_noprice`) | moved to A2 | `OW.rel` (`outerTest = false` branch), `outerStep_OW` |
| `tbound : ts.length + count ≤ C0 + [rem = 0]` | `inner_*`, `outer_body` | vanished | emit tests coincide under `WR.trades`; walk fuel: `innerRun_ok` (`pot`, extra) |
| `cnt : count ≤ C0` | `sinv_drop`, `outer_body` | one walk frame lemma | `outerRun_fr` + `fr_facts` + `count_of_view` |
| `hashid : no hashed id = r.id` | `sinv_drop` | one walk frame lemma | `outerRun_fr` + `fr_facts` + `idOnBook_of_view` |
| `remle : rem ≤ qty` | `inner_*` (`K.remle`) | one walk frame lemma | `outerRun_fr` (`WFr.rem`) |
| `inv : Inv s` | `outer_body` | remains | `WO.inv` (`w_outer_body`) |
| `own : absSide own = c.own` | `outer_body` (`Frame.absSide_other`) | remains, in the identity | `WO.book` (`book_step`, `free_absSide_other`) |
| `cview : absSide contra ≈ contra` | `outer_body` | remains, in the identity | `WO.book` (`free_absSide`, `wr_split`) |
| `trades : ts = strades.map tradeObs` | `inner_fill` | remains, in the identity | `WO.trades` / `WR.trades` |
| `stopX : stop → ¬ crosses` | `outer_body` (`stopX_of_best`) | remains (store form of the walk's exit clause) | `WO.stopX` (`stopX_of_best` in `w_outer_body`) |

Inner (`IInv`, `Inner.lean:187`) against `WR`: `spec`, `aggr`, `shape` → A2 (`step_sim`, `IR`); `tbound` → vanished; `SInv.empty`/`head` (reference contra list vs store) → vanished (`bookView` identity keeps the empty head level on both sides); `SInv.inv`/`frame`/`cnt`/`hashid` → `WR.inv` + frame per step (`best_frame`), `cnt`/`hashid` via `WFr`; `best`, `passive` → `WR.bestL`, `WR.passive`; `stop`, `trades`, `remle` → `WR.stop`, `WR.trades`, `WFr.rem`; measure `imeasure` → none (induction on the budget).

## 5. Store operations by branch

Program inner-loop paths (C:111-153) and the contract calls on each:

| Operation | Contract calls | CANCEL_NEW | CANCEL_OLD | CANCEL_BOTH | DEC full | DEC part | FILL full | FILL part | Paths |
|---|---|---|---|---|---|---|---|---|---|
| read account | `order_get_account` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 7 |
| next | `queue_next` | | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 6 |
| **pop head** | `queue_remove` + `hash_remove` + `order_free` (3 calls) | | ✓ | ✓ | ✓ | | ✓ | | 4 (12 calls) |
| read remaining | `order_get_remaining` ×2 | | | | ✓ | ✓ | ✓ | ✓ | 4 (8 calls) |
| write remaining | `order_set_remaining` | | | | ✓ | ✓ | ✓ | ✓ | 4 |
| trade | `order_get_id`, `level_get_price`, `ME_trade_emit` | | | | | | ✓ | ✓ | 2 (6 calls) |

Outer iteration: `*_best` (every iteration), `level_get_price` (non-empty tree), `queue_first` (crossing), `level_get_count` (crossing), `*_remove` + `level_free` (emptied level: 2 calls).

The same operations in the two proofs (applications, definitions excluded):

| Store step | Direct lemma (uses in `Inner`+`Outer`) | Walk lemma (uses in `RefineInner`+`RefineOuter`) |
|---|---|---|
| pop head: store facts | `dropS_facts` 3 | `dropS_facts` 3 |
| pop head: invariant | `sinv_drop` 3 (InvM + frame + reference contra list) | `invM_drop` 3 (InvM only) |
| pop head: view | inside `sinv_drop` | `view_drop` 3, `book_step` |
| write remaining: invariant | `sinv_setRem` 2 | `invM_setRem` 2 |
| write remaining: view | inside `sinv_setRem` | `view_setRem` 2, `book_step` |
| first half of DEC/FILL | `core_facts` 2 | `wcore` 3 (incl. trap) |
| any head-level change: view | per branch | `book_step` 5 (one lemma) |
| free emptied level | `ev_free` 1, `free_*` | `ev_free` 1, `free_*` (same lemmas) |

## 6. Outputs of the walk route with no direct counterpart

| Output | Where | Use |
|---|---|---|
| Certified code-shaped spec `Walk.process` | `Spec.lean` (C line ↔ Lean line table), `process_agree` | executable oracle (`walk_diff.sh` D1/D2; a `walk_oracle` exe for `tests/differential/run.sh` is an option), documentation of the C in spec types |
| Trade list equal as full `Trade` records, cancel equal exactly | `process_agree`, `cancel_eq` | stronger than `obsSpec` |
| Two-directional trap correspondence | `w_inner_loop`, `w_outer_loop`, `w_inner_body_trap`, `w_outer_body_trap`, `LogicInv` | the program's `me_trap(2)`/`me_trap(3)` happen exactly where the walk returns `none` |
| Continuation device separated into Lean-only lemmas | A2 (`step_sim`, `OW`) | refinement relation with no reference-state clause (`WR`, `WO`) |
| Walk-only fuel and frame facts | `run_fuel_sufficient`, `outerRun_fr` | bounds proved once on the spec, used through the view |
| `WF_of_Inv` | `WFInv.lean` | the decoded store satisfies a spec-side well-formedness predicate |
| Differential fill streams | `Check.lean`, `walk_diff.sh` | exercise the capacity reject (Phase 3's cap-20 stream does not) |

## 7. Recommendation

| Option | For | Against |
|---|---|---|
| Keep both: direct as the record, walk as the second proof | two proofs by different architectures of the same statement, independent on the matching path; the walk adds §6 | every `Program.lean` change is re-proved twice: direct (`Inner`/`Outer`/`Accept` continuation lemmas) and walk (`Spec` transliteration, A3 refinement, A2 equivalence) |
| Replace direct by walk | refinement part mechanical (A3 is mechanical except `book_step`); no invented invariant | route-specific lines 2,901 vs 1,480; content moves to A2 (1,319 lines) rather than disappearing |
| Drop the walk | one proof to maintain | loses §6 outputs |

Recommendation: **keep both, `main`'s direct proof as the record, the walk proof as the second proof.** Reasons from the tables: (i) the walk route's refinement step (A3, 1,582 lines) is the same size as the direct route's specific part (1,480) and mechanical, so re-proving it after a program change is procedure, not design; (ii) its content (A2) is Lean-only and does not change when only the program's store handling changes; (iii) route-specific cost is twice the direct route's, so it does not replace it; (iv) §6 outputs (certified code-shaped oracle, trap correspondence) exist only on the walk route.

Maintenance cost of keeping both: a change to `Program.lean` requires (a) re-transliterating `Walk.Spec` (and re-running D1/D2), (b) re-proving the affected A3 lemmas (mechanical), (c) re-proving A2 if the walk's step changes (content), and (d) re-proving the direct route's affected continuation lemmas. PLAN-W §6 (one definition parametric in `BookOps`, with a syntactic instance) would remove (a) and (b); decide separately.

Sessions: A0 1, A1 1, A2 1, A3a 1, A3b 1, A4 1.

