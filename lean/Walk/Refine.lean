import Walk.RefineOuter

/-!
# A3b: the program refines the walk; `matcher_refines` as a corollary

* `w_side_run`: the side function (post-only, `rem := qty`, outer loop,
  resting step, `return`) against `Walk.sideProc`.
* `Walk.refines`: for every request, the program run refines
  `Walk.process` on the decoded book (`WRefines`).
* `Walk.matcher_refines`: `main`'s `matcher_refines`, statement verbatim,
  from `Walk.refines` and A2's `process_agree`.

Scope, as in the A4 totals: the entry rejections (static, duplicate,
capacity) and cancel are `main`'s `refines_static`/`refines_duplicate`/
`refines_capacity` (`Refines.lean`) and `refines_cancel` (`Cancel.lean`),
outside both routes' specific files. On those cases `Walk.process` returns
exactly `processB`'s result (A2: `processOrder_entry`, `cancel_eq`), so they
are reused, not re-proved. The walk route's own work is the accepted order.
-/

namespace Walk

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel
  MatcherStore MatcherLoop MatcherInner MatcherOuter MatcherRest MatcherAccept MatcherRun

variable {S : Type} [EngineDb S]

open EngineDb

-- ============================================================================
-- Facts that pass through the view
-- ============================================================================

theorem count_of_view {X Y : BookState} (h : bookView X = bookView Y) : count X = count Y := by
  have hb := side_views h .bids
  have ha := side_views h .asks
  have e : ∀ L : List PriceLevel, (L.flatMap (·.orders)).length = ((L.map levelView).flatMap (·.orders)).length := by
    intro L; induction L with
    | nil => rfl
    | cons l ls ih => simp [levelView, ih]
  simp only [count, allBookOrders, List.length_append]
  rw [e X.bids, e X.asks, e Y.bids, e Y.asks]
  simp only [sideL] at hb ha
  rw [hb, ha]

theorem levelsUsed_of_view {X Y : BookState} (h : bookView X = bookView Y) :
    levelsUsed X = levelsUsed Y := by
  have hb := congrArg List.length (side_views h .bids)
  have ha := congrArg List.length (side_views h .asks)
  simp only [List.length_map, sideL] at hb ha
  simp [levelsUsed, hb, ha]

theorem idOnBook_of_view {X Y : BookState} (h : bookView X = bookView Y) (n : Nat) :
    idOnBook X n = idOnBook Y n := by
  have hb := side_views h .bids
  have ha := side_views h .asks
  have e : ∀ L : List PriceLevel, (L.flatMap (·.orders)).any (·.id == n) =
      ((L.map levelView).flatMap (·.orders)).any (·.id == n) := by
    intro L; induction L with
    | nil => rfl
    | cons l ls ih => simp [levelView, ih, orderView, List.any_map, Function.comp_def]
  simp only [idOnBook, allBookOrders, List.any_append]
  rw [e X.bids, e X.asks, e Y.bids, e Y.asks]
  simp only [sideL] at hb ha
  rw [hb, ha]

theorem idOnBook_sides (c : Ctx) (b : BookState) (n : Nat) :
    idOnBook b n = true ↔ n ∈ ids (sideL b c.own) ∨ n ∈ ids (sideL b c.contra) := by
  constructor
  · intro h
    simp only [idOnBook, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨o, ho, hon⟩ := h
    have := (allIds c b).subset (List.mem_map_of_mem (f := (·.id)) ho)
    rw [hon] at this
    exact List.mem_append.mp this
  · intro h
    have hm := (allIds c b).symm.subset (List.mem_append.mpr h)
    obtain ⟨o, ho, hon⟩ := List.mem_map.mp hm
    simp only [idOnBook, List.any_eq_true, beq_iff_eq]
    exact ⟨o, ho, hon⟩

/-- A match only removes orders: no new id, no more orders. -/
theorem fr_facts {c : Ctx} {st st' : State} (hf : WFr c st st') :
    count st'.book ≤ count st.book ∧ (∀ n, idOnBook st'.book n = true → idOnBook st.book n = true) := by
  refine ⟨?_, fun n h => ?_⟩
  · rw [count_sides c st'.book, count_sides c st.book, hf.own]
    have := hf.sub.length_le; omega
  · rw [idOnBook_sides c] at h ⊢
    rw [hf.own] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (hf.sub.subset h)

-- ============================================================================
-- The walk's resting step, as one equation
-- ============================================================================

theorem rest_accept {c : Ctx} {st : State} (hr : 0 < st.rem) (h2 : c.r.orderType ≠ 2)
    (h1 : c.r.orderType ≠ 1) (hcnt : ¬ c.cap ≤ count st.book)
    (hlev : ¬ c.cap ≤ levelsUsed st.book) (hdup : (hashFind st.book c.r.id.toNat).isSome = false)
    (hsorted : (sideL st.book c.own).Pairwise (fun x y => prioB c.own x.price y.price = true)) :
    ∃ bk, rest c st = (.accepted, bk) ∧
      sideL bk c.own = insSpec c.own (sideL st.book c.own) (restOrder c st.rem) c.r.price.toNat ∧
      sideL bk c.contra = sideL st.book c.contra ∧ bk.stops = st.book.stops := by
  have happ : ∀ y : PriceLevel,
      ((fun l : PriceLevel => { l with orders := l.orders ++ [restOrder c st.rem] }) y).price = y.price :=
    fun _ => rfl
  cases hf : tFind st.book c.own c.r.price.toNat with
  | some lv =>
    refine ⟨_, rest_found hr h2 h1 hcnt hdup hf, ?_, ?_, ?_⟩
    · simp only [qInsertTail, sideL_setSideL]
      rw [modAt_eq_map hsorted]
      have hex : ∃ y ∈ sideL st.book c.own, y.price = c.r.price.toNat := by
        obtain ⟨hp1, -⟩ := List.find?_eq_some_iff_append.mp hf
        exact ⟨lv, List.mem_of_find?_eq_some hf, by simpa using hp1⟩
      rw [insSpec_exists c.own _ _ _ hsorted hex]
      rfl
    · simp [qInsertTail, sideL_setSideL_ne c.own_ne.symm]
    · simp [qInsertTail]
  | none =>
    have hfresh : ∀ y ∈ sideL st.book c.own, y.price ≠ c.r.price.toNat := by
      intro y hy e
      unfold tFind at hf
      rw [List.find?_eq_none] at hf
      exact hf y hy (by simp [e])
    refine ⟨_, rest_fresh hr h2 h1 hcnt hlev hdup hf, ?_, ?_, ?_⟩
    · simp only [qInsertTail, tInsertNew, sideL_setSideL]
      rw [modAt_insLevel happ hfresh, insSpec_fresh c.own _ _ _ hfresh]; rfl
    · simp [qInsertTail, tInsertNew, sideL_setSideL_ne c.own_ne.symm]
    · simp [qInsertTail, tInsertNew]

/-- `insSpec` respects the view. -/
theorem insSpec_views (t : Tree) {L1 L2 : List PriceLevel} {o1 o2 : Order} (p : Nat)
    (hL : L1.map levelView = L2.map levelView) (ho : orderView o1 = orderView o2) :
    (insSpec t L1 o1 p).map levelView = (insSpec t L2 o2 p).map levelView := by
  rw [views_iff] at hL ⊢
  have hn : nO o1 = nO o2 := by rw [nO_eq, nO_eq, ho]
  cases t
  · simp only [insSpec]; rw [insertDesc_nL, insertDesc_nL, hL, hn]
  · simp only [insSpec]; rw [insertAsc_nL, insertAsc_nL, hL, hn]

-- ============================================================================
-- The side function
-- ============================================================================

/-- After the post-only check: `rem := qty`, the outer loop, the resting step
    and `return ACCEPTED`, against the rest of `Walk.sideProc`. -/
theorem w_side_cont (hcap : CapOk S) {s : S} {r : CRequest} (hI : Inv s) (hst : Static r)
    (hdup : EngineDb.hashFind s r.id = none)
    (hnf : ¬ ((r.orderType = 0 ∨ r.orderType = 3) ∧ capacity (S := S) ≤ EngineDb.count s))
    {isBuy : Bool} (hbuy : isBuy = decide (r.side = 0)) (L0 : Loc) (hst0 : L0.stop = false)
    {st : State}
    (hrun : outerRun (wctx S r isBuy) (capacity (S := S) + 1)
      { book := absBook (view s), rem := r.qty.toNat, stop := false, trades := [] } = some st) :
    ∃ st1, Eval program (Stmt.block [.assign "rem" (v "qty"), outerLoop isBuy, restStmt isBuy,
        retc .accepted]) (mkSt s r L0 []) (st1, .ret (.code (codeOf (rest (wctx S r isBuy) st).1))) ∧
      st1.trades = st.trades.map tradeObs ∧
      bookView (absBook (view st1.store)) = bookView (rest (wctx S r isBuy) st).2 ∧
      Inv st1.store := by
  let c := wctx S r isBuy
  let b := absBook (view s)
  have hWF := WF_of_Inv hI hcap
  have hq0 : 0 < r.qty.toNat := by
    have := hst.qty
    exact Nat.pos_of_ne_zero (fun e => this (UInt64.toNat_inj.mp (by simpa using e)))
  let L1 : Loc := { L0 with rem := r.qty }
  have e1 : Eval program (.assign "rem" (v "qty")) (mkSt s r L0 []) (mkSt s r L1 [], .normal) :=
    ev_assign (by lsimp) (set_rem r L0 r.qty)
  have hW0 : WO r isBuy s L1 [] { book := b, rem := r.qty.toNat, stop := false, trades := [] } :=
    ⟨hI, rfl, rfl, hst0, rfl, fun h => by simp [L1, hst0] at h⟩
  obtain ⟨s1, L2, eloop, hW1⟩ := (w_outer_loop hcap hW0).1 st hrun
  have hfr := outerRun_fr hrun
  obtain ⟨hcntW, hidW⟩ := fr_facts hfr
  have hfin := outerRun_final hrun
  have e3tail : ∀ {st : St S}, Eval program (retc .accepted) st (st, .ret (.code (codeOf .accepted))) :=
    fun {st} => Eval.retcode (st := st) .accepted
  have hw1 := hW1.inv.wf
  -- through the view: the store after matching against the walk's book
  have hcnt_view : count (absBook (view s1)) = count st.book := count_of_view hW1.book
  have hbS : count b = EngineDb.count s := by
    rw [count_eq_bookSize rfl, bookSize_absBook]; exact hI.count_eq.symm
  have hs1S : count (absBook (view s1)) = EngineDb.count s1 := by
    rw [count_eq_bookSize rfl, bookSize_absBook]; exact hW1.inv.count_eq.symm
  have hnoid : idOnBook st.book r.id.toNat = false := by
    cases h : idOnBook st.book r.id.toNat
    · rfl
    · exfalso
      have h1 := hidW _ h
      have h2 := (hashFind_isSome_iff hI r.id).mpr h1
      rw [hdup] at h2; cases h2
  have hdup1 : EngineDb.hashFind s1 r.id = none := by
    cases h : EngineDb.hashFind s1 r.id with
    | none => rfl
    | some x =>
      exfalso
      have h1 := (hashFind_isSome_iff hW1.inv r.id).mp (by rw [h]; rfl)
      rw [idOnBook_of_view hW1.book, hnoid] at h1; cases h1
  have hid1 : ∀ h ∈ (view s1).hash, (view s1).orderId h ≠ r.id := by
    have := hashFind_law s1 r.id hw1; rw [hdup1] at this; exact this
  by_cases hrest : L2.rem ≠ 0 ∧ r.orderType ≠ 2 ∧ r.orderType ≠ 1
  · obtain ⟨hr0, hi, hm⟩ := hrest
    have hty03 : r.orderType = 0 ∨ r.orderType = 3 := by
      rcases hst.ty with h | h | h | h
      · exact Or.inl h
      · exact absurd h hm
      · exact absurd h hi
      · exact Or.inr h
    have hlt : EngineDb.count s < capacity (S := S) := by
      by_cases h : capacity (S := S) ≤ EngineDb.count s
      · exact absurd ⟨hty03, h⟩ hnf
      · omega
    have hcnt1 : EngineDb.count s1 < capacity (S := S) := by
      have : count st.book ≤ count b := hcntW
      omega
    have hremN : 0 < st.rem := by
      rw [← hW1.rem]
      exact Nat.pos_of_ne_zero (fun e => hr0 (UInt64.toNat_inj.mp (by rw [e]; rfl)))
    -- the program's resting step
    obtain ⟨s3, L3, h, hf, hRV, hw3, hc3, erest⟩ :=
      rest_run (r := r) (L := L2) (ts := st.trades.map tradeObs) isBuy hW1.inv hcnt1 hid1 hr0 hi hm
    -- the walk's resting step
    have hlevW : ¬ c.cap ≤ levelsUsed st.book := by
      show ¬ capacity (S := S) ≤ _
      rw [← levelsUsed_of_view hW1.book]
      have := levels_le_count hW1.inv.client
      have := hW1.inv.count_eq
      have e : levelsUsed (absBook (view s1)) = ((view s1).tree .bids ++ (view s1).tree .asks).length := by
        simp only [levelsUsed, absBook, absSide, List.length_append]
        rw [(sortLevels_perm .bids _).length_eq, (sortLevels_perm .asks _).length_eq]; simp
      rw [e]; omega
    have hsorted : (sideL st.book c.own).Pairwise (fun x y => prioB c.own x.price y.price = true) := by
      rw [hfr.own]; exact hWF.sorted c.own
    obtain ⟨bk, hrv, hbo, hbc, hbs⟩ := rest_accept (c := c) hremN hi hm
      (by show ¬ capacity (S := S) ≤ _; omega)
      hlevW (by rw [hashFind_isSome]; exact hnoid) hsorted
    rw [hrv]
    have hstop : L2.stop = true := by
      have := hfin; simp [outerTest] at this
      rw [hW1.stop]; exact this hremN
    refine ⟨mkSt s3 r L3 (st.trades.map tradeObs), Eval.block_cons_normal e1 (Eval.block_cons_normal eloop
      (Eval.block_cons_normal erest e3tail (by simp)) (by simp)) (by simp), rfl, ?_, ?_⟩
    · -- the book
      have hov : ∀ n, orderView (restOrder c st.rem) =
          orderView (restingOrder (ownT isBuy) (r.restRow L2.rem) n) := by
        intro n
        have hside : sideOfTree (ownT isBuy) = if r.side = 0 then .buy else .sell := by
          subst hbuy; by_cases h0 : r.side = 0 <;> simp [h0, ownT, sideOfTree]
        simp only [orderView, restOrder, restingOrder, CRequest.restRow, OrderView.mk.injEq, c, wctx]
        rw [hside, ← hW1.rem]
        simp
      obtain ⟨hown3, hcon3⟩ := rest_book hw1 hf hRV hov
      simp only [mkSt]
      rw [bookView_sides]
      have hB := hW1.book
      rw [bookView_sides] at hB
      have hownv : (sideL (absBook (view s3)) (ownT isBuy)).map levelView =
          (sideL bk (ownT isBuy)).map levelView := by
        rw [sideL_absBook, hown3, show ownT isBuy = c.own from rfl, hbo]
        exact insSpec_views _ _ (by rw [← sideL_absBook]; exact side_views hW1.book _) rfl
      have hconv : (sideL (absBook (view s3)) (contraT isBuy)).map levelView =
          (sideL bk (contraT isBuy)).map levelView := by
        rw [sideL_absBook, hcon3, show contraT isBuy = c.contra from rfl, hbc, ← sideL_absBook]
        exact side_views hW1.book _
      refine ⟨?_, ?_, ?_⟩
      · cases hb : isBuy
        · have := hconv; simp only [hb, contraT, Bool.false_eq_true, if_false] at this; exact this
        · have := hownv; simp only [hb, ownT, if_true] at this; exact this
      · cases hb : isBuy
        · have := hownv; simp only [hb, ownT, Bool.false_eq_true, if_false] at this; exact this
        · have := hconv; simp only [hb, contraT, if_true] at this; exact this
      · rw [hbs, hfr.stops]; rfl
    · -- the invariant
      refine rest_inv hW1.inv hcnt1 hf hRV hw3 hc3 ?_ rfl ?_ ?_ ?_ ?_ ?_
      · show r.side = sideCode (ownT isBuy)
        subst hbuy; rcases hst.side with h | h <;> simp [h, ownT, sideCode]
      · exact pos_of_ne hr0
      · show L2.rem ≤ r.qty
        rw [UInt64.le_iff_toNat_le, hW1.rem]; exact hfr.rem
      · show r.stpMode ≤ 4
        rcases hst.stp with h | h | h | h | h <;> rw [h] <;> decide
      · exact pos_of_ne (hst.price hm)
      · intro y hy
        have hx : ¬ crossB isBuy ((view s1).levelPrice y) r.price := hW1.stopX hstop hm y hy
        cases isBuy <;> simp only [crossB, Bool.false_eq_true, if_false, if_true] at hx ⊢ <;>
          rw [UInt64.le_iff_toNat_le] at hx <;> rw [UInt64.lt_iff_toNat_lt] <;> omega
  · have hnr : ¬ (0 < st.rem ∧ c.r.orderType ≠ 2 ∧ c.r.orderType ≠ 1) := by
      rintro ⟨h0, h2, h1⟩
      exact hrest ⟨fun e => by rw [← hW1.rem, e] at h0; simp at h0, h2, h1⟩
    rw [rest_none hnr]
    have ernr : Eval program (restStmt isBuy) (mkSt s1 r L2 (st.trades.map tradeObs))
        (mkSt s1 r L2 (st.trades.map tradeObs), .normal) := by
      refine Eval.when_false (ev_restCond_false ?_)
      by_cases h0 : L2.rem = 0
      · exact Or.inl h0
      · by_cases h2 : r.orderType = 2
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Classical.byContradiction fun h1 => hrest ⟨h0, h2, h1⟩))
    exact ⟨mkSt s1 r L2 (st.trades.map tradeObs), Eval.block_cons_normal e1 (Eval.block_cons_normal eloop
      (Eval.block_cons_normal ernr e3tail (by simp)) (by simp)) (by simp), rfl, hW1.book, hW1.inv⟩

/-- **The side function** against `Walk.sideProc`. -/
theorem w_side_run (hcap : CapOk S) {s : S} {r : CRequest} (hI : Inv s) (hst : Static r)
    (hdup : EngineDb.hashFind s r.id = none)
    (hnf : ¬ ((r.orderType = 0 ∨ r.orderType = 3) ∧ capacity (S := S) ≤ EngineDb.count s))
    {isBuy : Bool} (hbuy : isBuy = decide (r.side = 0)) {w : ResultCode × ProcessResult}
    (hw : sideProc (wctx S r isBuy) (absBook (view s)) = some w) :
    ∃ st1 k, Eval program (sideFun isBuy).body (mkSt s r {} []) (st1, .ret (.code k)) ∧
      k = codeOf w.1 ∧ st1.trades = w.2.trades.map tradeObs ∧
      bookView (absBook (view st1.store)) = bookView w.2.book ∧ Inv st1.store := by
  have hwf := hI.wf
  rw [sideFun_body]
  have hb : (wctx S r isBuy).bound = some (capacity (S := S) + 1) := by
    unfold CapOk at hcap; simp [Ctx.bound, wctx, hcap]
  -- the matching phase, once the post-only check has passed with locals `L0`
  have cont : ∀ (L0 : Loc), L0.stop = false →
      ¬ ((wctx S r isBuy).r.orderType = 3 ∧ postOnlyCross (wctx S r isBuy) (absBook (view s)) = true) →
      Eval program (poStmt isBuy) (mkSt s r {} []) (mkSt s r L0 [], .normal) →
      ∃ st1 k, Eval program (Stmt.block [poStmt isBuy, .assign "rem" (v "qty"), outerLoop isBuy,
          restStmt isBuy, retc .accepted]) (mkSt s r {} []) (st1, .ret (.code k)) ∧
        k = codeOf w.1 ∧ st1.trades = w.2.trades.map tradeObs ∧
        bookView (absBook (view st1.store)) = bookView w.2.book ∧ Inv st1.store := by
    intro L0 hL0 hpo epo
    unfold sideProc at hw
    rw [if_neg hpo, hb] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    cases hrun : outerRun (wctx S r isBuy) (capacity (S := S) + 1)
        { book := absBook (view s), rem := (wctx S r isBuy).r.qty.toNat, stop := false, trades := [] } with
    | none => rw [hrun] at hw; cases hw
    | some st =>
      rw [hrun] at hw
      simp only [Option.bind_some, Option.some.injEq] at hw
      subst hw
      obtain ⟨st1, ecnt, htr, hbk, hinv⟩ := w_side_cont hcap hI hst hdup hnf hbuy L0 hL0 hrun
      exact ⟨st1, _, Eval.block_cons_normal epo ecnt (by simp), rfl, htr, hbk, hinv⟩
  by_cases h3 : r.orderType = 3
  · have e_tb := ev_tBest (P := program) (s := s) (r := r) (L := ({} : Loc)) (ts := []) (contraT isBuy)
    have eq3 : evalExpr (mkSt s r ({} : Loc) []) (eqc "otype" OT_POST_ONLY) = .ok (.bool true) := by
      lsimp [h3]
    have hlaw := EngineDb.tBest_law s (contraT isBuy) hwf
    cases hbst : EngineDb.tBest s (contraT isBuy) with
    | none =>
      rw [hbst] at hlaw e_tb
      have htree : (view s).tree (contraT isBuy) = [] := hlaw
      have hpc : postOnlyCross (wctx S r isBuy) (absBook (view s)) = false := by
        unfold postOnlyCross
        rw [tBest_eq, wctx_contra, sideL_absBook]
        simp [absSide, htree, sortLevels]
      apply cont { ({} : Loc) with best := none } rfl (by rw [hpc]; simp)
      exact Eval.when_true eq3 (Eval.block_cons_normal e_tb
        (Eval.when_false (ev_poCond_none (s := s) (r := r) (L := { ({} : Loc) with best := none })
          (ts := []) isBuy rfl)) (by simp))
    | some l =>
      rw [hbst] at hlaw e_tb
      obtain ⟨hl, hlb⟩ := hlaw
      have hll : liveL (view s) l = true := hwf.tree_live _ _ hl
      obtain ⟨lrow, hlrow⟩ : ∃ lrow, readLevel s l = some lrow := by
        rw [readLevel_law]; simp only [liveL] at hll; exact Option.isSome_iff_exists.mp hll
      have hlp : (view s).levelPrice l = lrow.price := by
        rw [readLevel_law] at hlrow; simp [Db.levelPrice, hlrow]
      have econd := ev_poCond_some (s := s) (r := r) (L := { ({} : Loc) with best := some l }) (ts := [])
        isBuy rfl hll hlrow
      have hpc : postOnlyCross (wctx S r isBuy) (absBook (view s)) = decide (crossB isBuy lrow.price r.price) := by
        unfold postOnlyCross
        rw [tBest_eq, wctx_contra, sideL_absBook, absSide_best hwf hl hlb, List.head?_cons]
        simp only [absLevel, hlp]
        by_cases h : crossB isBuy lrow.price r.price
        · rw [decide_eq_true h]; exact (crosses_iff (S := S) (r := r) (isBuy := isBuy) lrow.price).mpr h
        · rw [decide_eq_false h]
          cases hc : (wctx S r isBuy).crosses lrow.price.toNat
          · rfl
          · exact absurd ((crosses_iff (S := S) (r := r) (isBuy := isBuy) lrow.price).mp hc) h
      by_cases hcx : crossB isBuy lrow.price r.price
      · -- crossing: rejected, nothing changes
        have hpo : (wctx S r isBuy).r.orderType = 3 ∧
            postOnlyCross (wctx S r isBuy) (absBook (view s)) = true := ⟨h3, by rw [hpc]; simp [hcx]⟩
        unfold sideProc at hw
        rw [if_pos hpo] at hw
        simp only [Option.some.injEq] at hw; subst hw
        refine ⟨mkSt s r { ({} : Loc) with best := some l } [], _, ?_, rfl, rfl, rfl, hI⟩
        exact Eval.block_cons_ret (Eval.when_true eq3 (Eval.block_cons_normal e_tb
          (Eval.block_cons_ret (Eval.when_true (by rw [econd, decide_eq_true hcx])
            (Eval.retcode .rejectedPostOnly))) (by simp)))
      · apply cont { ({} : Loc) with best := some l } rfl (by rw [hpc]; simp [hcx])
        exact Eval.when_true eq3 (Eval.block_cons_normal e_tb
          (Eval.when_false (by rw [econd, decide_eq_false hcx])) (by simp))
  · exact cont {} rfl (fun h => h3 h.1) (ev_po_skip isBuy h3)

-- ============================================================================
-- The entry function and the theorem
-- ============================================================================

/-- **The program refines the walk** on one request: the run returns the
    walk's result code, trades and book view, and `Inv` holds again. -/
def WRefines (s : S) (req : Req) : Prop :=
  ∃ w, Walk.process (capacity (S := S)) (absBook (view s)) req = some w ∧
    ∃ f s' ts, runEntry program f (entryOf req) (argsOf req) s = .ok (.code (codeOf w.1), s', ts) ∧
      ts = w.2.trades.map tradeObs ∧ bookView (absBook (view s')) = bookView w.2.book ∧ Inv s'

/-- An accepted order: the entry glue of `main`'s `refines_accept`, with the
    walk's side function. -/
theorem w_refines_accept (hcap : CapOk S) {s : S} {r : CRequest} (hI : Inv s)
    (hn : staticCode (capacity (S := S)) r = none) (hd : ¬(EngineDb.hashFind s r.id).isSome = true)
    (hnf : ¬((r.orderType = 0 ∨ r.orderType = 3) ∧ capacity (S := S) ≤ EngineDb.count s))
    {w : ResultCode × ProcessResult}
    (hw : sideProc (wctx S r (decide (r.side = 0))) (absBook (view s)) = some w) :
    ∃ f s' ts, runEntry program f (entryOf (.order r)) (argsOf (.order r)) s =
        .ok (.code (codeOf w.1), s', ts) ∧
      ts = w.2.trades.map tradeObs ∧ bookView (absBook (view s')) = bookView w.2.book ∧ Inv s' := by
  have hdn : EngineDb.hashFind s r.id = none := by
    cases h : EngineDb.hashFind s r.id
    · rfl
    · rw [h] at hd; exact absurd rfl hd
  let isBuy := decide (r.side = 0)
  obtain ⟨st1, k, ebody, hk, htr, hbk, hinv⟩ := w_side_run hcap hI (static_of hn) hdn hnf rfl hw
  have ecall := ev_call_side (s := s) (r := r) isBuy ebody
  have eite : Eval program (.ite (eqc "side" SIDE_BUY)
      (.call (some "r") "gen_process_buy" [v "id", v "account", v "side", v "otype", v "stp", v "price", v "qty"])
      (.call (some "r") "gen_process_sell" [v "id", v "account", v "side", v "otype", v "stp", v "price", v "qty"]))
      (dupSt s r) ({ st1 with env := dupEnvR r (EngineDb.hashFind s r.id) k }, .normal) := by
    by_cases h0 : r.side = 0
    · have hb : isBuy = true := by simp [isBuy, h0]
      rw [hb] at ecall
      exact Eval.ite_true (by simp (config := {decide := true}) [dupSt, dupEnv, eqc, b2, v, c, evalExpr,
        lookupVar, List.lookup, evalBin, h0, SIDE_BUY, bind, Except.bind]) ecall
    · have hb : isBuy = false := by simp [isBuy, h0]
      rw [hb] at ecall
      exact Eval.ite_false (by simp (config := {decide := true}) [dupSt, dupEnv, eqc, b2, v, c, evalExpr,
        lookupVar, List.lookup, evalBin, h0, SIDE_BUY, bind, Except.bind]) ecall
  have eret : Eval program (.ret (v "r")) ({ st1 with env := dupEnvR r (EngineDb.hashFind s r.id) k } : St S)
      ({ st1 with env := dupEnvR r (EngineDb.hashFind s r.id) k }, .ret (.code k)) :=
    Eval.ret (by simp (config := {decide := true}) [dupEnvR, v, evalExpr, lookupVar, List.lookup])
  have hbody : Eval program (Stmt.block (processOrderStmts.drop 6)) (orderSt s r)
      ({ st1 with env := dupEnvR r (EngineDb.hashFind s r.id) k }, .ret (.code k)) := by
    simp only [processOrderStmts, List.drop]
    exact Eval.block_cons_normal (eval_dup s r)
      (Eval.block_cons_normal (Eval.when_pass (ev_dupcheck s r) hd)
        (Eval.block_cons_normal (Eval.when_pass (ev_capcheck s r hcap hI.count_le) hnf)
          (Eval.block_cons_normal eite eret (by simp)) (by simp)) (by simp)) (by simp)
  obtain ⟨f, hrun⟩ := order_run ((prefix_run hcap s r).2 hn _ hbody)
  exact ⟨f, st1.store, st1.trades, by rw [← hk]; exact hrun, htr, hbk, hinv⟩

/-- A request on which the walk agrees exactly with `processB` inherits
    `main`'s refinement. -/
theorem wrefines_of_refines {s : S} {req : Req} (hR : Refines s req)
    (hp : Walk.process (capacity (S := S)) (absBook (view s)) req = some (specStep s req)) :
    WRefines s req :=
  ⟨_, hp, hR⟩

/-- **`Walk.refines`**: for every store satisfying `Inv` and every request, the
    program refines the walking spec. -/
theorem refines (hcap : CapOk S) {s : S} (hI : Inv s) (req : Req) : WRefines s req := by
  have hWF := WF_of_Inv hI hcap
  cases req with
  | cancel id =>
    exact wrefines_of_refines (refines_cancel id hI hcap)
      (by show some (cancel _ id) = _; rw [cancel_eq hWF id]; rfl)
  | order r =>
    have hleft : ∀ (hR : Refines s (.order r)),
        (¬ ∃ o, r.toSpec = some o ∧ o.id = r.id.toNat ∧ idOnBook (absBook (view s)) o.id = false ∧
          ¬ (requestMayRest r = true ∧ capacity (S := S) ≤ bookSize (absBook (view s))) ∧
          staticCode (capacity (S := S)) r = none ∧
          processOrder (capacity (S := S)) (absBook (view s)) r =
            sideProc { cap := capacity (S := S), r := r, isBuy := decide (r.side = 0) } (absBook (view s)) ∧
          processB (capacity (S := S)) (absBook (view s)) (.order r) =
            (postOnlyCode o (absBook (view s)), processWithId (absBook (view s)) o)) →
        WRefines s (.order r) := by
      intro hR hnot
      rcases processOrder_entry (r := r) hWF with ⟨w, hw1, hw2⟩ | hright
      · exact wrefines_of_refines hR (by show processOrder _ _ r = _; rw [hw1, hw2]; rfl)
      · exact absurd hright hnot
    cases hsc : staticCode (EngineDb.capacity (S := S)) r with
    | some c =>
      exact hleft (refines_static hI hcap hsc) (fun ⟨_, _, _, _, _, h, _⟩ => by rw [hsc] at h; cases h)
    | none =>
      by_cases hd : (EngineDb.hashFind s r.id).isSome = true
      · refine hleft (refines_duplicate hI hcap hsc hd) (fun ⟨o, _, hid, hno, _⟩ => ?_)
        have := (hashFind_isSome_iff hI r.id).mp hd
        rw [← hid, hno] at this; cases this
      · by_cases hf : (r.orderType = 0 ∨ r.orderType = 3) ∧ EngineDb.capacity (S := S) ≤ EngineDb.count s
        · refine hleft (refines_capacity hI hcap hsc hd hf) (fun ⟨o, _, _, _, hcp, _⟩ => ?_)
          apply hcp
          refine ⟨requestMayRest_iff.mpr hf.1, ?_⟩
          rw [bookSize_absBook, ← hI.count_eq]; exact hf.2
        · -- accepted by the entry checks: the walk's side function
          have hpo : processOrder (capacity (S := S)) (absBook (view s)) r =
              sideProc (wctx S r (decide (r.side = 0))) (absBook (view s)) := by
            rw [processOrder_eq hWF.cap64, hsc]
            simp only
            have h1 : (hashFind (absBook (view s)) r.id.toNat).isSome = false := by
              rw [hashFind_isSome]
              cases e : idOnBook (absBook (view s)) r.id.toNat
              · rfl
              · exact absurd ((hashFind_isSome_iff hI r.id).mpr e) hd
            have h2 : ¬ ((r.orderType = 0 ∨ r.orderType = 3) ∧
                capacity (S := S) ≤ count (absBook (view s))) := by
              rw [count_eq_bookSize rfl, bookSize_absBook, ← hI.count_eq]; exact hf
            rw [if_neg (by rw [h1]; simp), if_neg h2]; rfl
          obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
            (run_fuel_sufficient (.order r) hWF.cap64 hWF.count hWF.nonempty)
          have hw' : sideProc (wctx S r (decide (r.side = 0))) (absBook (view s)) = some w := by
            rw [← hpo]; exact hw
          exact ⟨w, hw, w_refines_accept hcap hI hsc hd hf hw'⟩

/-- **`matcher_refines`** (`main`'s statement, verbatim), as a corollary of
    `Walk.refines` and A2's `process_agree`. -/
theorem matcher_refines {S : Type} [EngineDb S] (hcap : CapOk S) {s : S} (hI : Inv s) (req : Req) :
    Refines s req := by
  obtain ⟨w, hw, f, s', ts, hrun, htr, hbk, hinv⟩ := refines hcap hI req
  obtain ⟨w', hw', hcode, htrades, hnB⟩ := process_agree (WF_of_Inv hI hcap) req
  rw [hw] at hw'; cases hw'
  have hsp : specStep s req = processB (capacity (S := S)) (absBook (view s)) req := rfl
  refine ⟨f, s', ts, ?_, ?_, ?_, hinv⟩
  · rw [hsp, ← hcode]; exact hrun
  · rw [hsp, htr, htrades]
  · rw [hsp, hbk]; exact (bookView_iff _ _).mpr hnB

end Walk
