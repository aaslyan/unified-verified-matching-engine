import Walk.RefineInner

/-!
# A3b: the program's outer loop refines the walk's

`WO`, the relation at outer-iteration boundaries: `Inv s` (`main`'s, no empty
level), the identity clauses of `WR` (`bookView`, `rem`, `stop`, trades), and
the walk's exit clause on the store: once `stop` is set, no contra level
crosses (for the resting step's uncrossedness; `main`'s `stopX_of_best`).

The facts the resting step needs about the whole match (the book only lost
orders; `rem` only went down) are proved on the walk alone (`innerRun_fr`,
`outerRun_fr`) and carried to the store through the view.
-/

namespace Walk

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel
  MatcherStore MatcherLoop MatcherInner MatcherOuter

variable {S : Type} [EngineDb S]

open EngineDb

-- ============================================================================
-- Walk frame: a match only removes contra orders and lowers `rem`
-- ============================================================================

/-- `st'` is `st` after some matching: the own side and stops unchanged, the
    contra ids a sublist, `rem` not larger. -/
structure WFr (c : Ctx) (st st' : State) : Prop where
  own   : sideL st'.book c.own = sideL st.book c.own
  stops : st'.book.stops = st.book.stops
  sub   : (ids (sideL st'.book c.contra)).Sublist (ids (sideL st.book c.contra))
  rem   : st'.rem ≤ st.rem

theorem WFr.refl (c : Ctx) (st : State) : WFr c st st :=
  ⟨rfl, rfl, List.Sublist.refl _, Nat.le_refl _⟩

theorem WFr.trans {c : Ctx} {a b d : State} (h₁ : WFr c a b) (h₂ : WFr c b d) : WFr c a d :=
  ⟨h₂.own.trans h₁.own, h₂.stops.trans h₁.stops, h₂.sub.trans h₁.sub, Nat.le_trans h₂.rem h₁.rem⟩

theorem innerStep_rem_le {c : Ctx} {st st' : State} (hs : innerStep c st = some st') :
    st'.rem ≤ st.rem := by
  unfold innerStep at hs
  split at hs
  · simp only [Option.some.injEq] at hs; subst hs; exact Nat.le_refl _
  · split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact Nat.le_refl _
    · split at hs
      · split at hs
        · simp only [Option.some.injEq] at hs; subst hs; exact Nat.zero_le _
        · split at hs
          · split at hs <;> (simp only [Option.some.injEq] at hs; subst hs) <;> simp
          · simp only [Option.some.injEq] at hs; subst hs; exact Nat.sub_le _ _
      · split at hs
        · simp only [Option.some.injEq] at hs; subst hs; exact Nat.sub_le _ _
        · cases hs

theorem innerStep_stop {c : Ctx} {st st' : State} (hs : innerStep c st = some st') :
    st'.stop = st.stop := by
  unfold innerStep at hs
  split at hs
  · simp only [Option.some.injEq] at hs; subst hs; rfl
  · split at hs
    · simp only [Option.some.injEq] at hs; subst hs; rfl
    · split at hs
      · split at hs
        · simp only [Option.some.injEq] at hs; subst hs; rfl
        · split at hs
          · split at hs <;> (simp only [Option.some.injEq] at hs; subst hs) <;> rfl
          · simp only [Option.some.injEq] at hs; subst hs; rfl
      · split at hs
        · simp only [Option.some.injEq] at hs; subst hs; rfl
        · cases hs

theorem innerRun_stop {c : Ctx} : ∀ {n : Nat} {st st' : State}, innerRun c n st = some st' →
    st'.stop = st.stop
  | 0, st, st', h => by
    unfold innerRun at h; split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; rfl
  | n + 1, st, st', h => by
    unfold innerRun at h; split at h
    · cases hs : innerStep c st with
      | none => rw [hs] at h; cases h
      | some s1 => rw [hs] at h; exact (innerRun_stop h).trans (innerStep_stop hs)
    · simp only [Option.some.injEq] at h; subst h; rfl

theorem innerStep_fr {c : Ctx} {st st' : State} (hs : innerStep c st = some st') : WFr c st st' := by
  cases h : sideL st.book c.contra with
  | nil =>
    have : innerStep c st = some st := by simp [innerStep, tBest_eq, h]
    rw [this] at hs; cases hs; exact WFr.refl c _
  | cons L R =>
    obtain ⟨L1, h1, -, hsub, hown, hstops, -⟩ := innerStep_frame h hs
    exact ⟨hown, hstops, by rw [h1, h, ids_cons, ids_cons]; exact hsub.append (List.Sublist.refl _),
      innerStep_rem_le hs⟩

theorem innerRun_fr {c : Ctx} : ∀ {n : Nat} {st st' : State}, innerRun c n st = some st' → WFr c st st'
  | 0, st, st', h => by
    unfold innerRun at h; split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; exact WFr.refl c _
  | n + 1, st, st', h => by
    unfold innerRun at h; split at h
    · cases hs : innerStep c st with
      | none => rw [hs] at h; cases h
      | some s1 => rw [hs] at h; exact (innerStep_fr hs).trans (innerRun_fr h)
    · simp only [Option.some.injEq] at h; subst h; exact WFr.refl c _

theorem outerStep_fr {c : Ctx} {st st' : State} (hs : outerStep c st = some st') : WFr c st st' := by
  unfold outerStep at hs
  split at hs
  · simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, List.Sublist.refl _, Nat.le_refl _⟩
  · split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl, List.Sublist.refl _, Nat.le_refl _⟩
    · cases hb : c.bound with
      | none => rw [hb] at hs; cases hs
      | some n =>
        rw [hb] at hs
        simp only [Option.bind_eq_bind, Option.bind_some] at hs
        cases hin : innerRun c n st with
        | none => rw [hin] at hs; cases hs
        | some s1 =>
          rw [hin] at hs
          simp only [Option.bind_some] at hs
          have h1 := innerRun_fr hin
          split at hs
          · rename_i best' hb'
            split at hs
            · rename_i hz
              simp only [Option.some.injEq] at hs; subst hs
              refine h1.trans ⟨?_, ?_, ?_, Nat.le_refl _⟩
              · simp only [dropBest, own_frame]
              · simp [dropBest]
              · rw [tBest_eq] at hb'
                cases hc : sideL s1.book c.contra with
                | nil => rw [hc] at hb'; cases hb'
                | cons L R =>
                  rw [hc] at hb'
                  simp only [List.head?_cons, Option.some.injEq] at hb'
                  rw [← hb'] at hz
                  have : L.orders = [] := List.eq_nil_of_length_eq_zero hz
                  simp [ids_cons, hc, this]
            · simp only [Option.some.injEq] at hs; subst hs; exact h1
          · simp only [Option.some.injEq] at hs; subst hs; exact h1

theorem outerRun_fr {c : Ctx} : ∀ {n : Nat} {st st' : State}, outerRun c n st = some st' → WFr c st st'
  | 0, st, st', h => by
    unfold outerRun at h; split at h
    · cases h
    · simp only [Option.some.injEq] at h; subst h; exact WFr.refl c _
  | n + 1, st, st', h => by
    unfold outerRun at h; split at h
    · cases hs : outerStep c st with
      | none => rw [hs] at h; cases h
      | some s1 => rw [hs] at h; exact (outerStep_fr hs).trans (outerRun_fr h)
    · simp only [Option.some.injEq] at h; subst h; exact WFr.refl c _

-- ============================================================================
-- The outer relation
-- ============================================================================

/-- **The outer-loop relation.** -/
structure WO (r : CRequest) (isBuy : Bool) (s : S) (L : Loc) (ts : List TradeObs)
    (st : State) : Prop where
  inv    : Inv s
  book   : bookView (absBook (view s)) = bookView st.book
  rem    : L.rem.toNat = st.rem
  stop   : L.stop = st.stop
  trades : ts = st.trades.map tradeObs
  stopX  : L.stop = true → r.orderType ≠ 1 →
    ∀ x ∈ (view s).tree (contraT isBuy), ¬ crossB isBuy ((view s).levelPrice x) r.price

theorem crosses_iff {r : CRequest} {isBuy : Bool} (bp : UInt64) :
    (wctx S r isBuy).crosses bp.toNat = true ↔ crossB isBuy bp r.price := by
  unfold Ctx.crosses crossB wctx
  cases isBuy <;> simp [UInt64.le_iff_toNat_le]

theorem side_views {X Y : BookState} (h : bookView X = bookView Y) (t : Tree) :
    (sideL X t).map levelView = (sideL Y t).map levelView := by
  rw [bookView_sides] at h; cases t; exact h.1; exact h.2.1

/-- **The outer body.** One outer iteration of the program, from a state
    related to `st` where the outer test holds, is one `outerStep`. -/
theorem w_outer_body (hcap : CapOk S) {r : CRequest} {isBuy : Bool} {s : S} {L : Loc}
    {ts : List TradeObs} {st st1 : State} (hW : WO r isBuy s L ts st)
    (ht : outerTest st = true) (hs : outerStep (wctx S r isBuy) st = some st1) :
    ∃ s' L', Eval program (outerBody isBuy) (mkSt s r L ts)
        (mkSt s' r L' (st1.trades.map tradeObs), .normal) ∧
      WO r isBuy s' L' (st1.trades.map tradeObs) st1 := by
  have hw := hW.inv.wf
  have htr : st.trades.map tradeObs = ts := hW.trades.symm
  have hstp : st.stop = false := by simp [outerTest] at ht; exact ht.2
  have e1 := ev_tBest (P := program) (s := s) (r := r) (L := L) (ts := ts) (contraT isBuy)
  have hlaw := EngineDb.tBest_law s (contraT isBuy) hw
  have hsv := side_views hW.book (contraT isBuy)
  rw [sideL_absBook] at hsv
  unfold outerStep at hs
  rw [wctx_contra, tBest_eq] at hs
  cases hbest : EngineDb.tBest s (contraT isBuy) with
  | none =>
    rw [hbest] at hlaw e1
    have htree : (view s).tree (contraT isBuy) = [] := hlaw
    have hnil : sideL st.book (contraT isBuy) = [] := by
      have : absSide (view s) (contraT isBuy) = [] := by simp [absSide, htree, sortLevels]
      rw [this] at hsv; exact List.map_eq_nil_iff.mp hsv.symm
    rw [hnil] at hs
    simp only [List.head?_nil, Option.some.injEq] at hs; subst hs
    refine ⟨s, { L with best := none, stop := true }, ?_, ⟨hW.inv, hW.book, hW.rem, rfl, rfl,
      fun _ _ x hx => by rw [htree] at hx; cases hx⟩⟩
    dsimp only; rw [htr]
    exact Eval.block_cons_normal e1 (Eval.ite_true (by rw [ev_bestNull]; rfl) ev_stop) (by simp)
  | some l =>
    rw [hbest] at hlaw e1
    obtain ⟨hl, hlb⟩ := hlaw
    have hll : liveL (view s) l = true := hw.tree_live _ _ hl
    obtain ⟨lrow, hlrow⟩ : ∃ lrow, readLevel s l = some lrow := by
      rw [readLevel_law]; simp only [liveL] at hll; exact Option.isSome_iff_exists.mp hll
    have hlp : (view s).levelPrice l = lrow.price := by
      rw [readLevel_law] at hlrow; simp [Db.levelPrice, hlrow]
    have hsplit := absSide_best hw hl hlb
    rw [hsplit] at hsv
    obtain ⟨L0, R, hside, hlv0, hR⟩ : ∃ L0 R, sideL st.book (contraT isBuy) = L0 :: R ∧
        levelView L0 = levelView (absLevel (view s) (contraT isBuy) l) ∧
        R.map levelView = (restSide (view s) (contraT isBuy) l).map levelView := by
      cases hc : sideL st.book (contraT isBuy) with
      | nil => rw [hc] at hsv; simp at hsv
      | cons L0 R =>
        rw [hc] at hsv; simp only [List.map_cons, List.cons.injEq] at hsv
        exact ⟨L0, R, rfl, hsv.1.symm, hsv.2.symm⟩
    have hp0 : L0.price = lrow.price.toNat := by
      have := congrArg LevelView.price hlv0
      simp only [levelView, absLevel] at this; rw [this, hlp]
    rw [hside] at hs
    simp only [List.head?_cons] at hs
    have ecross := ev_crossCond (s := s) (r := r) (ts := ts) (L := { L with best := some l })
      isBuy rfl hll hlrow
    have hcx : (wctx S r isBuy).crosses L0.price = true ↔ crossB isBuy lrow.price r.price := by
      rw [hp0]; exact crosses_iff lrow.price
    by_cases hx : r.orderType ≠ 1 ∧ ¬ crossB isBuy lrow.price r.price
    · -- no crossing: stop
      rw [if_pos (show (wctx S r isBuy).r.orderType ≠ 1 ∧ ¬ (wctx S r isBuy).crosses L0.price = true
        from ⟨hx.1, fun h => hx.2 (hcx.mp h)⟩)] at hs
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨s, { L with best := some l, stop := true }, ?_, ⟨hW.inv, hW.book, hW.rem, rfl, rfl,
        fun _ _ => stopX_of_best hlb (by rw [hlp]; exact hx.2)⟩⟩
      dsimp only; rw [htr]
      exact Eval.block_cons_normal e1 (Eval.ite_false (by rw [ev_bestNull]; rfl)
        (Eval.ite_true (by rw [ecross, decide_eq_true hx]) ev_stop)) (by simp)
    · -- crossing: the inner loop on level `l`, then the cleanup
      rw [if_neg (show ¬((wctx S r isBuy).r.orderType ≠ 1 ∧ ¬ (wctx S r isBuy).crosses L0.price = true)
        from fun h => hx ⟨h.1, fun h' => h.2 (hcx.mpr h')⟩)] at hs
      have hb : (wctx S r isBuy).bound = some (capacity (S := S) + 1) := by
        unfold CapOk at hcap; simp [Ctx.bound, wctx, hcap]
      rw [hb] at hs
      simp only [Option.bind_eq_bind, Option.bind_some] at hs
      have hqf : EngineDb.qFirst s l = ((view s).queue l).head? := qFirst_law s l hw hll
      have e2 := ev_qFirst (P := program) (s := s) (r := r) (ts := ts) (L := { L with best := some l })
        rfl hll
      rw [hqf] at e2
      have hWR : WR r isBuy l s { L with best := some l, passive := ((view s).queue l).head? } ts st :=
        ⟨Inv.toM hW.inv l, hl, hlb, hW.book, hW.rem, hW.stop, hW.trades, rfl, fun _ => rfl⟩
      cases hin : innerRun (wctx S r isBuy) (capacity (S := S) + 1) st with
      | none => rw [hin] at hs; cases hs
      | some st' =>
        rw [hin] at hs
        simp only [Option.bind_some] at hs
        obtain ⟨s', L', eloop, hW'⟩ := (w_inner_loop hcap hWR).1 st' hin
        have hw' := hW'.inv.wf
        have hin' := hW'.mem
        have hll' : liveL (view s') l = true := hw'.tree_live _ _ hin'
        obtain ⟨L0', R', hside', hlv', hR'⟩ := wr_split hW'
        rw [tBest_eq, hside', List.head?_cons] at hs
        simp only at hs
        have hcnt : levelCount L0' = ((view s').queue l).length := by
          rw [levelView_absLevel] at hlv'
          have := congrArg (fun v : LevelView => v.orders.length) hlv'
          simpa [levelView, levelCount] using this
        have eall : ∀ {s'' : S}, Eval program (freeStmt isBuy)
            (mkSt s' r L' (st'.trades.map tradeObs)) (mkSt s'' r L' (st'.trades.map tradeObs), .normal) →
            Eval program (outerBody isBuy) (mkSt s r L ts)
              (mkSt s'' r L' (st'.trades.map tradeObs), .normal) := fun ef =>
          Eval.block_cons_normal e1 (Eval.ite_false (by rw [ev_bestNull]; rfl)
            (Eval.ite_false (by rw [ecross, decide_eq_false hx])
              (Eval.block_cons_normal e2 (Eval.block_cons_normal eloop ef (by simp)) (by simp))))
            (by simp)
        have hstop' : L'.stop = false := by rw [hW'.stop]; rw [innerRun_stop hin]; exact hstp
        by_cases he' : (view s').queue l = []
        · -- the level emptied: free it
          rw [if_pos (by rw [hcnt, he']; rfl)] at hs
          simp only [Option.some.injEq] at hs; subst hs
          obtain ⟨efree, hv'', hw'', hcnt'', hlu''⟩ :=
            ev_free isBuy (r := r) (L := L') (ts := st'.trades.map tradeObs) hW'.bestL hw' hin' he'
          have hIM := hW'.inv
          refine ⟨_, L', eall efree, ⟨⟨hw'', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hW'.rem, hW'.stop, rfl,
            fun h => by rw [hstop'] at h; cases h⟩⟩
          · rw [hv'']; exact free_clientInv hw' hIM.client hin' he'
          · intro y; rw [hv'']; exact hIM.orders_resting y
          · rw [hv'']; exact free_levels_resting hw' hin' hIM.levels_resting
          · rw [hcnt'', hv'', free_restingCount hw' hin' he']; exact hIM.count_eq
          · have := free_tree_length (db := view s') (t := contraT isBuy) hin'
            have := hIM.levels_eq
            rw [hv'']; omega
          · rw [hcnt'']; exact hIM.count_le
          · rw [hv'', bookView_sides]
            have hB := hW'.book
            rw [bookView_sides] at hB
            have hcon : (sideL (absBook (freeDb (view s') (contraT isBuy) l)) (contraT isBuy)).map levelView =
                (sideL (dropBest st'.book (contraT isBuy)) (contraT isBuy)).map levelView := by
              rw [sideL_absBook, free_absSide hw' hin', sideL_dropBest, hside', List.tail_cons, hR']
            have hoth : ∀ t', t' ≠ contraT isBuy →
                (sideL (absBook (freeDb (view s') (contraT isBuy) l)) t').map levelView =
                (sideL (dropBest st'.book (contraT isBuy)) t').map levelView := by
              intro t' ht'
              rw [sideL_absBook, free_absSide_other hw' hin' ht', dropBest, sideL_setSideL_ne ht',
                ← sideL_absBook]
              cases t'; exact hB.1; exact hB.2.1
            refine ⟨?_, ?_, ?_⟩
            · cases hcb : contraT isBuy
              · rw [← hcb]; exact hcon
              · rw [← hcb]; exact hoth .bids (by rw [hcb]; decide)
            · cases hcb : contraT isBuy
              · rw [← hcb]; exact hoth .asks (by rw [hcb]; decide)
              · rw [← hcb]; exact hcon
            · simp only [dropBest, stops_setSideL]; exact hB.2.2
        · -- the level keeps orders
          rw [if_neg (by rw [hcnt]; exact fun e => he' (List.length_eq_zero_iff.mp e))] at hs
          simp only [Option.some.injEq] at hs; subst hs
          have hI' := hW'.inv.toInv he'
          have efree := ev_nofree isBuy (r := r) (L := L') (ts := st'.trades.map tradeObs) hW'.bestL
            hll' he' (count_le_cap_lc hI' hin' hcap)
          exact ⟨s', L', eall efree, ⟨hI', hW'.book, hW'.rem, hW'.stop, rfl,
            fun h => by rw [hstop'] at h; cases h⟩⟩

-- ============================================================================
-- The outer body's trap, and the outer loop
-- ============================================================================

/-- **The outer body's trap.** Where one walk outer iteration is `none` (its
    inner loop is), the program's outer body has no run. -/
theorem w_outer_body_trap (hcap : CapOk S) {r : CRequest} {isBuy : Bool} {s : S} {L : Loc}
    {ts : List TradeObs} {st : State} (hW : WO r isBuy s L ts st)
    (hs : outerStep (wctx S r isBuy) st = none) :
    ∀ res, ¬ Eval program (outerBody isBuy) (mkSt s r L ts) res := by
  intro res hev
  have hw := hW.inv.wf
  have e1 := ev_tBest (P := program) (s := s) (r := r) (L := L) (ts := ts) (contraT isBuy)
  have hlaw := EngineDb.tBest_law s (contraT isBuy) hw
  have hsv := side_views hW.book (contraT isBuy)
  rw [sideL_absBook] at hsv
  unfold outerStep at hs
  rw [wctx_contra, tBest_eq] at hs
  have hbody := seq_through e1 hev
  cases hbest : EngineDb.tBest s (contraT isBuy) with
  | none =>
    rw [hbest] at hlaw
    have htree : (view s).tree (contraT isBuy) = [] := hlaw
    have hnil : sideL st.book (contraT isBuy) = [] := by
      have : absSide (view s) (contraT isBuy) = [] := by simp [absSide, htree, sortLevels]
      rw [this] at hsv; exact List.map_eq_nil_iff.mp hsv.symm
    rw [hnil] at hs; cases hs
  | some l =>
    rw [hbest] at hlaw hbody
    obtain ⟨hl, hlb⟩ := hlaw
    have hll : liveL (view s) l = true := hw.tree_live _ _ hl
    obtain ⟨lrow, hlrow⟩ : ∃ lrow, readLevel s l = some lrow := by
      rw [readLevel_law]; simp only [liveL] at hll; exact Option.isSome_iff_exists.mp hll
    have hlp : (view s).levelPrice l = lrow.price := by
      rw [readLevel_law] at hlrow; simp [Db.levelPrice, hlrow]
    rw [absSide_best hw hl hlb] at hsv
    obtain ⟨L0, R, hside, hlv0⟩ : ∃ L0 R, sideL st.book (contraT isBuy) = L0 :: R ∧
        levelView L0 = levelView (absLevel (view s) (contraT isBuy) l) := by
      cases hc : sideL st.book (contraT isBuy) with
      | nil => rw [hc] at hsv; simp at hsv
      | cons L0 R =>
        rw [hc] at hsv; simp only [List.map_cons, List.cons.injEq] at hsv
        exact ⟨L0, R, rfl, hsv.1.symm⟩
    have hp0 : L0.price = lrow.price.toNat := by
      have := congrArg LevelView.price hlv0
      simp only [levelView, absLevel] at this; rw [this, hlp]
    rw [hside] at hs
    simp only [List.head?_cons] at hs
    have ecross := ev_crossCond (s := s) (r := r) (ts := ts) (L := { L with best := some l })
      isBuy rfl hll hlrow
    have hcx : (wctx S r isBuy).crosses L0.price = true ↔ crossB isBuy lrow.price r.price := by
      rw [hp0]; exact crosses_iff lrow.price
    by_cases hx : r.orderType ≠ 1 ∧ ¬ crossB isBuy lrow.price r.price
    · rw [if_pos (show (wctx S r isBuy).r.orderType ≠ 1 ∧ ¬ (wctx S r isBuy).crosses L0.price = true
        from ⟨hx.1, fun h => hx.2 (hcx.mp h)⟩)] at hs
      cases hs
    · rw [if_neg (show ¬((wctx S r isBuy).r.orderType ≠ 1 ∧ ¬ (wctx S r isBuy).crosses L0.price = true)
        from fun h => hx ⟨h.1, fun h' => h.2 (hcx.mpr h')⟩)] at hs
      have hb : (wctx S r isBuy).bound = some (capacity (S := S) + 1) := by
        unfold CapOk at hcap; simp [Ctx.bound, wctx, hcap]
      rw [hb] at hs
      simp only [Option.bind_eq_bind, Option.bind_some] at hs
      have hin : innerRun (wctx S r isBuy) (capacity (S := S) + 1) st = none := by
        cases h : innerRun (wctx S r isBuy) (capacity (S := S) + 1) st with
        | none => rfl
        | some st' =>
          rw [h] at hs; simp only [Option.bind_some] at hs
          split at hs
          · split at hs <;> cases hs
          · cases hs
      have hqf : EngineDb.qFirst s l = ((view s).queue l).head? := qFirst_law s l hw hll
      have e2 := ev_qFirst (P := program) (s := s) (r := r) (ts := ts) (L := { L with best := some l })
        rfl hll
      rw [hqf] at e2
      have hWR : WR r isBuy l s { L with best := some l, passive := ((view s).queue l).head? } ts st :=
        ⟨Inv.toM hW.inv l, hl, hlb, hW.book, hW.rem, hW.stop, hW.trades, rfl, fun _ => rfl⟩
      have trap := (w_inner_loop hcap hWR).2 hin
      rcases Eval.ite_inv hbody with ⟨hc, -⟩ | ⟨-, hb2⟩
      · rw [ev_bestNull] at hc; cases hc
      · rcases Eval.ite_inv hb2 with ⟨hc, -⟩ | ⟨-, hm⟩
        · rw [ecross, decide_eq_false hx] at hc; cases hc
        · simp only [matchBlock, Stmt.block] at hm
          have hm2 := seq_through e2 hm
          rcases Eval.seq_inv hm2 with ⟨x, hx1, -⟩ | ⟨v, hv, -⟩
          · exact trap _ hx1
          · exact trap _ hv

theorem ev_outerCond_walk {r : CRequest} {isBuy : Bool} {s : S} {L : Loc} {ts : List TradeObs}
    {st : State} (hW : WO r isBuy s L ts st) :
    evalExpr (mkSt s r L ts) outerCond = .ok (.bool (outerTest st)) := by
  rw [ev_outerCond]
  congr 2
  unfold outerTest
  rw [← hW.rem, ← hW.stop]
  simp [UInt64.lt_iff_toNat_lt]

theorem w_outer_run (hcap : CapOk S) {r : CRequest} {isBuy : Bool} :
    ∀ (n : Nat) (st st' : State) (s : S) (L : Loc) (ts : List TradeObs),
      outerRun (wctx S r isBuy) n st = some st' → WO r isBuy s L ts st →
      ∃ s' L', LoopRun program outerCond (outerBody isBuy) n (mkSt s r L ts)
          (mkSt s' r L' (st'.trades.map tradeObs), .normal) ∧
        WO r isBuy s' L' (st'.trades.map tradeObs) st' := by
  intro n
  induction n with
  | zero =>
    intro st st' s L ts hrun hW
    unfold outerRun at hrun
    split at hrun
    · cases hrun
    · rename_i ht
      simp only [Option.some.injEq] at hrun; subst hrun
      refine ⟨s, L, ?_, by rw [← hW.trades]; exact hW⟩
      rw [← hW.trades]
      exact .stop (by rw [ev_outerCond_walk hW]; simpa using ht)
  | succ n ih =>
    intro st st' s L ts hrun hW
    unfold outerRun at hrun
    split at hrun
    · rename_i ht
      cases hs : outerStep (wctx S r isBuy) st with
      | none => rw [hs] at hrun; cases hrun
      | some st1 =>
        rw [hs] at hrun
        simp only [Option.bind_some] at hrun
        obtain ⟨s1, L1, hev, hW1⟩ := w_outer_body hcap hW ht hs
        obtain ⟨s', L', hrun', hW'⟩ := ih st1 st' s1 L1 _ hrun hW1
        exact ⟨s', L', .step (by rw [ev_outerCond_walk hW, ht]) hev hrun', hW'⟩
    · rename_i ht
      simp only [Option.some.injEq] at hrun; subst hrun
      refine ⟨s, L, ?_, by rw [← hW.trades]; exact hW⟩
      rw [← hW.trades]
      exact .stop (by rw [ev_outerCond_walk hW]; simpa using ht)

theorem w_outer_run_none (hcap : CapOk S) {r : CRequest} {isBuy : Bool} :
    ∀ (n : Nat) (st : State) (s : S) (L : Loc) (ts : List TradeObs),
      outerRun (wctx S r isBuy) n st = none → WO r isBuy s L ts st →
      ∀ res, ¬ LoopRun program outerCond (outerBody isBuy) n (mkSt s r L ts) res := by
  intro n
  induction n with
  | zero =>
    intro st s L ts hrun hW res hl
    unfold outerRun at hrun
    split at hrun
    · rename_i ht
      cases hl with
      | stop hc => rw [ev_outerCond_walk hW, ht] at hc; cases hc
    · cases hrun
  | succ n ih =>
    intro st s L ts hrun hW res hl
    unfold outerRun at hrun
    split at hrun
    · rename_i ht
      have hct : evalExpr (mkSt s r L ts) outerCond = .ok (.bool true) := by
        rw [ev_outerCond_walk hW, ht]
      cases hs : outerStep (wctx S r isBuy) st with
      | none =>
        have trap := w_outer_body_trap hcap hW hs
        cases hl with
        | stop hc => rw [hct] at hc; cases hc
        | step _ hb _ => exact trap _ hb
        | ret _ hb => exact trap _ hb
      | some st1 =>
        rw [hs] at hrun
        simp only [Option.bind_some] at hrun
        obtain ⟨s1, L1, hev, hW1⟩ := w_outer_body hcap hW ht hs
        cases hl with
        | stop hc => rw [hct] at hc; cases hc
        | step _ hb hrest =>
          have := Eval.det hev hb; cases this
          exact ih st1 s1 L1 _ hrun hW1 _ hrest
        | ret _ hb => have := Eval.det hev hb; cases this
    · cases hrun

/-- **The outer loop statement**, both directions, at the bound `capacity + 1`. -/
theorem w_outer_loop (hcap : CapOk S) {r : CRequest} {isBuy : Bool} {s : S} {L : Loc}
    {ts : List TradeObs} {st : State} (hW : WO r isBuy s L ts st) :
    (∀ st', outerRun (wctx S r isBuy) (capacity (S := S) + 1) st = some st' →
      ∃ s' L', Eval program (outerLoop isBuy) (mkSt s r L ts)
          (mkSt s' r L' (st'.trades.map tradeObs), .normal) ∧
        WO r isBuy s' L' (st'.trades.map tradeObs) st') ∧
    (outerRun (wctx S r isBuy) (capacity (S := S) + 1) st = none →
      ∀ res, ¬ Eval program (outerLoop isBuy) (mkSt s r L ts) res) := by
  refine ⟨fun st' hrun => ?_, fun hrun res hev => ?_⟩
  · obtain ⟨s', L', hl, hW'⟩ := w_outer_run hcap _ st st' s L ts hrun hW
    exact ⟨s', L', Eval.loop (boundVal_capPlus1' hcap) hl, hW'⟩
  · exact w_outer_run_none hcap _ st s L ts hrun hW res
      (loopRun_of_eval (boundVal_capPlus1' hcap) hev)

end Walk
