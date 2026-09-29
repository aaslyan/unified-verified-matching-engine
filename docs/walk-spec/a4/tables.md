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
