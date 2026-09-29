import Walk.EquivEntry

/-!
# A2, part 3: one walk step is one reference step

The reference's `doMatch` handles one resting order per call, as the walk's
inner iteration does. The two differ in bookkeeping only:

* the reference drops a level in the call that empties it; the walk keeps the
  empty level until the outer loop's cleanup. `normC` drops an empty head
  level, and the reference's contra side is `normC` of the walk's;
* the reference cancels the incoming order by status; the walk sets `rem = 0`
  (`IR`);
* after a partial fill the reference marks the maker `partiallyFilled`; the
  walk does not store a status. The two contra sides then agree up to `nL`
  (the view), and the match is over.

The relation to `doMatch` is through `MatcherSpec.rest` (the reference's
remaining computation at its own fuel) and the per-branch unfolding lemmas
`MatcherSpec.step_*`, both from `main`'s `SpecStep.lean`.
-/

namespace Walk

open EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherSpec MatcherInner MatcherRun

/-- The reference's test for "the match is over". -/
def done (inc : Order) : Bool := inc.remainingQty == 0 || inc.status == .cancelled

/-- A resting order the C can hold. -/
def Good (o : Order) : Prop :=
  0 < o.remainingQty ∧ o.visibleQty = o.remainingQty ∧ o.displayQty = none

/-- Drop an empty head level: the reference's view of the walk's contra side. -/
def normC : List PriceLevel → List PriceLevel
  | [] => []
  | l :: ls => if l.orders = [] then ls else l :: ls

theorem normC_cons_ne {l : PriceLevel} {ls : List PriceLevel} (h : l.orders ≠ []) :
    normC (l :: ls) = l :: ls := by simp [normC, h]

theorem normC_cons_nil {l : PriceLevel} {ls : List PriceLevel} (h : l.orders = []) :
    normC (l :: ls) = ls := by simp [normC, h]

/-- The request's spec order, as far as matching reads it. -/
structure CO (c : Ctx) (o1 : Order) : Prop where
  side   : o1.side = if c.isBuy then .buy else .sell
  price  : o1.price = if c.r.orderType = 1 then none else some c.r.price.toNat
  id     : o1.id = c.r.id.toNat
  po     : o1.postOnly = decide (c.r.orderType = 3)
  group  : o1.stpGroup = stpGroupOf c.r.account
  policy : o1.stpPolicy = stpPolicyOf c.r.account c.r.stpMode
  stp    : c.r.stpMode = 0 ∨ c.r.stpMode = 1 ∨ c.r.stpMode = 2 ∨ c.r.stpMode = 3 ∨
    c.r.stpMode = 4

/-- The walk's `rem` against the reference's incoming order. -/
structure IR (o1 : Order) (st : State) (inc : Order) : Prop where
  shape : IncShape o1 inc
  zero  : st.rem = 0 → done inc = true
  pos   : 0 < st.rem → inc.remainingQty = st.rem ∧ inc.status ≠ .cancelled

theorem IR.notDone {o1 inc : Order} {st : State} (h : IR o1 st inc) (hr : 0 < st.rem) :
    (inc.remainingQty == 0 || inc.status == .cancelled) = false := by
  obtain ⟨h1, h2⟩ := h.pos hr
  have e2 : (inc.status == .cancelled) = false := by
    cases hs : inc.status
    all_goals first | rfl | exact absurd hs h2
  have e1 : (inc.remainingQty == 0) = false := by
    rw [h1]; exact beq_false_of_ne (Nat.pos_iff_ne_zero.mp hr)
  rw [e1, e2]; rfl

-- ============================================================================
-- The request's tests against the reference's
-- ============================================================================

theorem u64_toNat_ne_zero {a : UInt64} (h : a ≠ 0) : a.toNat ≠ 0 := by
  intro e; exact h (UInt64.toNat_inj.mp (by simpa using e))

/-- The walk's STP test is `selfTradeConflict`. -/
theorem conflict_iff {c : Ctx} {o1 inc : Order} (hco : CO c o1) (hs : IncShape o1 inc) (p : Order) :
    (c.r.account ≠ 0 ∧ c.r.account.toNat = getAccount p ∧ c.r.stpMode ≠ 0) ↔
      selfTradeConflict inc p = true := by
  unfold selfTradeConflict getAccount
  rw [hs.policy, hs.group, hco.policy, hco.group]
  by_cases ha : c.r.account = 0
  · simp [ha, stpPolicyOf]
  · have hn := u64_toNat_ne_zero ha
    simp only [stpPolicyOf, stpGroupOf, ha, if_false, ne_eq, not_false_eq_true, true_and]
    have hpol : ((decodeStpMode c.r.stpMode).bind CStpMode.policy).isSome = true ↔
        c.r.stpMode ≠ 0 := by
      rcases hco.stp with h | h | h | h | h <;> rw [h] <;> decide
    cases hg : p.stpGroup with
    | none =>
      simp only [Option.getD_none, Bool.and_false, Bool.false_eq_true, iff_false, not_and]
      intro e; exact absurd e hn
    | some g =>
      simp only [Option.getD_some, Bool.and_eq_true, beq_iff_eq]
      rw [hpol]; exact And.comm

/-- The incoming order's policy, by STP mode, once a conflict exists. -/
theorem policy_of {c : Ctx} {o1 inc : Order} (hco : CO c o1) (hs : IncShape o1 inc)
    (ha : c.r.account ≠ 0) :
    (c.r.stpMode = 1 → inc.stpPolicy.getD .cancelNewest = .cancelNewest) ∧
    (c.r.stpMode = 2 → inc.stpPolicy.getD .cancelNewest = .cancelOldest) ∧
    (c.r.stpMode = 3 → inc.stpPolicy.getD .cancelNewest = .cancelBoth) ∧
    (c.r.stpMode = 4 → inc.stpPolicy.getD .cancelNewest = .decrement) := by
  rw [hs.policy, hco.policy]
  simp only [stpPolicyOf, ha, if_false]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [h] <;> rfl

/-- The walk's price test is `canMatchPrice`. -/
theorem canMatch_iff {c : Ctx} {o1 inc : Order} (hco : CO c o1) (hs : IncShape o1 inc) (bp : Nat) :
    canMatchPrice inc bp = true ↔ (c.r.orderType = 1 ∨ c.crosses bp = true) := by
  unfold canMatchPrice Ctx.crosses
  rw [hs.price, hs.side, hco.price, hco.side]
  by_cases h1 : c.r.orderType = 1
  · simp [h1]
  · simp only [h1, if_false, false_or]
    cases c.isBuy <;> simp [ge_iff_le]

/-- The walk's trade is the reference's. -/
theorem mkTrade_eq {c : Ctx} {o1 inc : Order} (hco : CO c o1) (hs : IncShape o1 inc)
    (L : PriceLevel) (p : Order) (q : Nat) :
    mkTrade c p L.price q = fillTrade inc L p q := by
  unfold mkTrade fillTrade
  rw [hs.id, hs.side, hs.group, hs.policy, hco.id, hco.side, hco.group, hco.policy]
  have hpo : inc.postOnly = o1.postOnly := by rw [hs]
  rw [hpo, hco.po]

-- ============================================================================
-- Book frame
-- ============================================================================

theorem Ctx.own_ne (c : Ctx) : c.own ≠ c.contra := by
  unfold Ctx.own Ctx.contra; cases c.isBuy <;> decide

theorem sideL_setSideL_ne {b : BookState} {t t' : Tree} {ls : List PriceLevel} (h : t' ≠ t) :
    sideL (setSideL b t ls) t' = sideL b t' := by
  cases t <;> cases t' <;> first | rfl | exact absurd rfl h

@[simp] theorem stops_setSideL (b : BookState) (t : Tree) (ls : List PriceLevel) :
    (setSideL b t ls).stops = b.stops := by cases t <;> rfl

theorem own_frame (c : Ctx) (b : BookState) (ls : List PriceLevel) :
    sideL (setSideL b c.contra ls) c.own = sideL b c.own := sideL_setSideL_ne c.own_ne

/-- Order ids of a list of levels, in order. -/
def ids (L : List PriceLevel) : List Nat := (L.flatMap (·.orders)).map (·.id)

-- ============================================================================
-- One inner iteration
-- ============================================================================

section Step

variable {c : Ctx} {o1 : Order} {own : List PriceLevel} {tm : Nat}

/-- **One walk step is one reference step.** At head level `L :: R` with head
    order `p :: os`, an inner iteration of the walk and one `doMatch` call keep
    the reference's remaining computation, and relate the new states. Either
    the head order left (`L1.orders = os`) and the reference's contra side is
    `normC` of the walk's, or the match is over and they agree up to the view. -/
theorem step_sim (hco : CO c o1) {st st1 : State} {inc : Order} {L : PriceLevel}
    {R : List PriceLevel} {p : Order} {os : List Order}
    (hs : innerStep c st = some st1) (h : sideL st.book c.contra = L :: R)
    (hp : L.orders = p :: os) (hg : Good p) (hprice : canMatchPrice o1 L.price = true)
    (hir : IR o1 st inc) (hrem : 0 < st.rem) :
    ∃ inc1 cref1 L1, IR o1 st1 inc1 ∧
      MatcherSpec.rest inc own (L :: R) st.trades tm =
        MatcherSpec.rest inc1 own cref1 st1.trades tm ∧
      sideL st1.book c.contra = L1 :: R ∧ L1.price = L.price ∧
      ((L1.orders = os ∧ cref1 = normC (L1 :: R)) ∨
        (st1.rem = 0 ∧ cref1.map nL = (normC (L1 :: R)).map nL)) ∧
      st1.stop = st.stop ∧ sideL st1.book c.own = sideL st.book c.own ∧
      st1.book.stops = st.book.stops := by
  obtain ⟨hr0, hvis, hdisp⟩ := hg
  obtain ⟨hinc, hnc⟩ := hir.pos hrem
  have hA : AtHead inc L p os :=
    ⟨hir.notDone hrem, by rw [canMatch_shape hir.shape]; exact hprice, hp,
      by rw [hvis]; exact Nat.pos_iff_ne_zero.mp hr0, hdisp⟩
  have hmin : min inc.remainingQty p.visibleQty = min st.rem p.remainingQty := by
    rw [hinc, hvis]
  have hown : ∀ ls, sideL (setSideL st.book c.contra ls) c.own = sideL st.book c.own :=
    fun ls => sideL_setSideL_ne c.own_ne
  unfold innerStep at hs
  rw [tBest_eq, h] at hs
  simp only [List.head?_cons, qFirst, hp] at hs
  by_cases hc : c.r.account ≠ 0 ∧ c.r.account.toNat = getAccount p ∧ c.r.stpMode ≠ 0
  · rw [if_pos hc] at hs
    have hsc := (conflict_iff hco hir.shape p).mp hc
    have hpol := policy_of hco hir.shape hc.1
    by_cases h1 : c.r.stpMode = 1
    · -- CANCEL_NEW
      rw [if_pos h1] at hs
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨{ inc with status := .cancelled }, L :: R, L,
        ⟨hir.shape.updSt _, fun _ => done_of_cancelled rfl, fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩,
        rest_step_done (step_cancelNew hA hsc (hpol.1 h1)) (done_of_cancelled rfl),
        h, rfl, Or.inr ⟨rfl, by rw [normC_cons_ne (by simp [hp])]⟩, rfl, rfl, rfl⟩
    · rw [if_neg h1] at hs
      by_cases h23 : c.r.stpMode = 2 ∨ c.r.stpMode = 3
      · rw [if_pos h23] at hs
        have hL1 : sideL (popHead st.book c.contra) c.contra =
            { L with orders := os } :: R := by simp [h, hp]
        by_cases h3 : c.r.stpMode = 3
        · -- CANCEL_BOTH
          rw [if_pos h3] at hs
          simp only [Option.some.injEq] at hs; subst hs
          refine ⟨{ inc with status := .cancelled }, drop1 L os R, { L with orders := os },
            ⟨hir.shape.updSt _, fun _ => done_of_cancelled rfl, fun h0 => absurd h0 (Nat.lt_irrefl 0)⟩,
            rest_step_done (step_cancelBoth hA hsc (hpol.2.2.1 h3)) (done_of_cancelled rfl),
            hL1, rfl, Or.inl ⟨rfl, ?_⟩, rfl, hown _, stops_setSideL _ _ _⟩
          unfold drop1 normC; rfl
        · -- CANCEL_OLD
          have h2 : c.r.stpMode = 2 := by rcases h23 with h | h; exact h; exact absurd h h3
          rw [if_neg h3] at hs
          simp only [Option.some.injEq] at hs; subst hs
          refine ⟨inc, drop1 L os R, { L with orders := os }, ⟨hir.shape, hir.zero, hir.pos⟩,
            rest_step (step_cancelOld hA hsc (hpol.2.1 h2)) (mm_drop1 hp _ _),
            hL1, rfl, Or.inl ⟨rfl, ?_⟩, rfl, hown _, stops_setSideL _ _ _⟩
          unfold drop1 normC; rfl
      · -- DECREMENT
        have h4 : c.r.stpMode = 4 := by
          rcases hco.stp with h | h | h | h | h
          · exact absurd h hc.2.2
          · exact absurd h h1
          · exact absurd (Or.inl h) h23
          · exact absurd (Or.inr h) h23
          · exact h
        rw [if_neg h23] at hs
        simp only [Option.some.injEq] at hs; subst hs
        have hstep_pol := hpol.2.2.2 h4
        by_cases hz : p.remainingQty - min st.rem p.remainingQty = 0
        · have hfull : p.remainingQty - min inc.remainingQty p.visibleQty = 0 := by rw [hmin]; exact hz
          have hstep := step_decrement_full (own := own) (rl := R) (trades := st.trades) (tm := tm)
            hA hsc hstep_pol hfull
          rw [hmin] at hstep
          have hL1 : sideL (if p.remainingQty - min st.rem p.remainingQty = 0 then
                popHead (setHeadRem st.book c.contra (p.remainingQty - min st.rem p.remainingQty))
                  c.contra
              else setHeadRem st.book c.contra (p.remainingQty - min st.rem p.remainingQty))
              c.contra = { L with orders := os } :: R := by
            rw [if_pos hz]; simp [h, hp]
          have hIR : ∀ bk : BookState, IR o1 { book := bk, rem := st.rem - min st.rem p.remainingQty, stop := st.stop, trades := st.trades } (decInc inc (min st.rem p.remainingQty)) := by
            intro bk
            refine ⟨hir.shape.upd _ _, fun h0 => ?_, fun h0 => ?_⟩
            · have h0' : st.rem - min st.rem p.remainingQty = 0 := h0
              simp [done, decInc, hinc, h0']
            · simp only [decInc, hinc]
              refine ⟨by first | rfl | trivial, ?_⟩
              rw [if_neg (Nat.pos_iff_ne_zero.mp h0)]; exact hnc
          by_cases hr : st.rem - min st.rem p.remainingQty = 0
          · refine ⟨_, _, { L with orders := os }, hIR _,
              rest_step_done hstep (by simp [decInc, hinc, hr]), hL1, rfl,
              Or.inl ⟨rfl, ?_⟩, rfl, ?_, ?_⟩
            · unfold drop1 normC; rfl
            · rw [if_pos hz]; simp only [popHead, setHeadRem, own_frame]
            · rw [if_pos hz]; simp [popHead, setHeadRem]
          · refine ⟨_, _, { L with orders := os }, hIR _,
              rest_step hstep (mm_drop1 hp _ _), hL1, rfl,
              Or.inl ⟨rfl, ?_⟩, rfl, ?_, ?_⟩
            · unfold drop1 normC; rfl
            · rw [if_pos hz]; simp only [popHead, setHeadRem, own_frame]
            · rw [if_pos hz]; simp [popHead, setHeadRem]
        · have hpart : p.remainingQty - min inc.remainingQty p.visibleQty ≠ 0 := by rw [hmin]; exact hz
          have hstep := step_decrement_part (own := own) (rl := R) (trades := st.trades) (tm := tm)
            hA hsc hstep_pol hpart
          rw [hmin, hvis] at hstep
          have hr : st.rem - min st.rem p.remainingQty = 0 := rem_zero_of_prem_pos hz
          let pv : Order := { p with remainingQty := p.remainingQty - min st.rem p.remainingQty, visibleQty := p.remainingQty - min st.rem p.remainingQty }
          refine ⟨_, _, { L with orders := pv :: os },
            ⟨hir.shape.upd _ _, fun _ => by simp [done, hinc, hr],
              fun h0 => by simp [hr] at h0⟩,
            rest_step_done hstep (by simp [hinc, hr]), ?_, rfl,
            Or.inr ⟨hr, ?_⟩, rfl, ?_, ?_⟩
          · rw [if_neg hz]; simp [h, hp, pv]
          · rw [normC_cons_ne (by simp)] <;> rfl
          · rw [if_neg hz]; simp only [setHeadRem, own_frame]
          · rw [if_neg hz]; simp [setHeadRem]
  · -- a fill
    rw [if_neg hc] at hs
    have hsc : selfTradeConflict inc p = false := by
      cases e : selfTradeConflict inc p
      · rfl
      · exact absurd ((conflict_iff hco hir.shape p).mpr e) hc
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      rw [mkTrade_eq hco hir.shape L p]
      by_cases hz : p.remainingQty - min st.rem p.remainingQty = 0
      · have hfull : p.remainingQty - min inc.remainingQty p.visibleQty = 0 := by rw [hmin]; exact hz
        have hstep := step_fill_full (own := own) (rl := R) (trades := st.trades) (tm := tm)
          hA hsc hfull
        rw [hmin, hinc] at hstep
        have hIR : ∀ (bk : BookState) (tr : List Trade), IR o1 { book := bk, rem := st.rem - min st.rem p.remainingQty, stop := st.stop, trades := tr } { inc with remainingQty := st.rem - min st.rem p.remainingQty } := by
          intro bk tr
          refine ⟨hir.shape.updRem _, fun h0 => ?_, fun h0 => ⟨rfl, hnc⟩⟩
          have h0' : st.rem - min st.rem p.remainingQty = 0 := h0
          simp [done, h0']
        have hL1 : sideL (if p.remainingQty - min st.rem p.remainingQty = 0 then
              popHead (setHeadRem st.book c.contra (p.remainingQty - min st.rem p.remainingQty))
                c.contra
            else setHeadRem st.book c.contra (p.remainingQty - min st.rem p.remainingQty))
            c.contra = { L with orders := os } :: R := by
          rw [if_pos hz]; simp [h, hp]
        have hmm : ∀ (i i' : Order), matchMeasure (drop1 L os R) i < matchMeasure (L :: R) i' :=
          mm_drop1 hp
        by_cases hr : st.rem - min st.rem p.remainingQty = 0
        · refine ⟨{ inc with remainingQty := st.rem - min st.rem p.remainingQty }, drop1 L os R, { L with orders := os }, hIR _ _, rest_step_done hstep (by simp [hr]), hL1, rfl,
            Or.inl ⟨rfl, ?_⟩, rfl, ?_, ?_⟩
          · unfold drop1 normC; rfl
          · rw [if_pos hz]; simp only [popHead, setHeadRem, own_frame]
          · rw [if_pos hz]; simp [popHead, setHeadRem]
        · refine ⟨{ inc with remainingQty := st.rem - min st.rem p.remainingQty }, drop1 L os R, { L with orders := os }, hIR _ _, rest_step hstep (hmm _ _), hL1, rfl,
            Or.inl ⟨rfl, ?_⟩, rfl, ?_, ?_⟩
          · unfold drop1 normC; rfl
          · rw [if_pos hz]; simp only [popHead, setHeadRem, own_frame]
          · rw [if_pos hz]; simp [popHead, setHeadRem]
      · have hpart : p.remainingQty - min inc.remainingQty p.visibleQty ≠ 0 := by rw [hmin]; exact hz
        have hstep := step_fill_part (own := own) (rl := R) (trades := st.trades) (tm := tm)
          hA hsc hpart
        rw [hmin, hvis, hinc] at hstep
        have hr : st.rem - min st.rem p.remainingQty = 0 := rem_zero_of_prem_pos hz
        let pv : Order := { p with remainingQty := p.remainingQty - min st.rem p.remainingQty, visibleQty := p.remainingQty - min st.rem p.remainingQty }
        refine ⟨{ inc with remainingQty := st.rem - min st.rem p.remainingQty }, _, { L with orders := pv :: os },
          ⟨hir.shape.updRem _, fun _ => by simp [done, hr], fun h0 => by simp [hr] at h0⟩,
          rest_step_done hstep (by simp [hr]), ?_, rfl, Or.inr ⟨hr, ?_⟩, rfl, ?_, ?_⟩
        · rw [if_neg hz]; simp [h, hp, pv]
        · rw [normC_cons_ne (by simp)]; simp [nL, nO, pv]
        · rw [if_neg hz]; simp only [setHeadRem, own_frame]
        · rw [if_neg hz]; simp [setHeadRem]
    · cases hs

end Step

-- ============================================================================
-- Walk frame: what one inner iteration does to the contra side's ids
-- ============================================================================

theorem ids_cons (l : PriceLevel) (ls : List PriceLevel) :
    ids (l :: ls) = l.orders.map (·.id) ++ ids ls := by simp [ids]

theorem sideCount_eq_ids (ls : List PriceLevel) : sideCount ls = (ids ls).length := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [ids_cons, ih]

/-- One inner iteration changes only the head level, and only shrinks its ids. -/
theorem innerStep_frame {c : Ctx} {st st1 : State} {L : PriceLevel} {R : List PriceLevel}
    (h : sideL st.book c.contra = L :: R) (hs : innerStep c st = some st1) :
    ∃ L1, sideL st1.book c.contra = L1 :: R ∧ L1.price = L.price ∧
      (L1.orders.map (·.id)).Sublist (L.orders.map (·.id)) ∧
      sideL st1.book c.own = sideL st.book c.own ∧ st1.book.stops = st.book.stops ∧
      st1.stop = st.stop := by
  have pop : ∀ (bk : BookState) (L' : PriceLevel), sideL bk c.contra = L' :: R →
      sideL (popHead bk c.contra) c.contra = { L' with orders := L'.orders.tail } :: R := by
    intro bk L' hb; simp [hb]
  have set : ∀ (bk : BookState) (q : Nat), sideL bk c.contra = L :: R →
      ∃ L1, sideL (setHeadRem bk c.contra q) c.contra = L1 :: R ∧ L1.price = L.price ∧
        L1.orders.map (·.id) = L.orders.map (·.id) := by
    intro bk q hb
    refine ⟨{ L with orders := match L.orders with | [] => [] | o :: os => { o with remainingQty := q, visibleQty := q } :: os }, ?_, rfl, ?_⟩
    · rw [sideL_setHeadRem, hb, modHead_cons]; congr 2
    cases L.orders <;> simp
  have tl : (L.orders.tail.map (·.id)).Sublist (L.orders.map (·.id)) := by
    cases L.orders <;> simp
  unfold innerStep at hs
  rw [tBest_eq, h] at hs
  simp only [List.head?_cons] at hs
  cases hq : qFirst L with
  | none =>
    rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
    exact ⟨L, h, rfl, List.Sublist.refl _, rfl, rfl, rfl⟩
  | some p =>
    rw [hq] at hs
    simp only at hs
    split at hs
    · split at hs
      · simp only [Option.some.injEq] at hs; subst hs
        exact ⟨L, h, rfl, List.Sublist.refl _, rfl, rfl, rfl⟩
      · split at hs
        · split at hs <;> (simp only [Option.some.injEq] at hs; subst hs) <;>
            exact ⟨_, pop _ _ h, rfl, tl, own_frame _ _ _, stops_setSideL _ _ _, rfl⟩
        · simp only [Option.some.injEq] at hs; subst hs
          obtain ⟨L1, h1, hp1, hi1⟩ := set st.book (p.remainingQty - min st.rem p.remainingQty) h
          split
          · refine ⟨_, pop _ _ h1, hp1, ?_, ?_, ?_, rfl⟩
            · have : (L1.orders.tail.map (·.id)).Sublist (L1.orders.map (·.id)) := by
                cases L1.orders <;> simp
              rw [← hi1]; exact this
            · simp only [popHead, setHeadRem, own_frame]
            · simp [popHead, setHeadRem]
          · exact ⟨L1, h1, hp1, hi1 ▸ List.Sublist.refl _, by simp only [setHeadRem, own_frame],
              by simp [setHeadRem], rfl⟩
    · split at hs
      · simp only [Option.some.injEq] at hs; subst hs
        obtain ⟨L1, h1, hp1, hi1⟩ := set st.book (p.remainingQty - min st.rem p.remainingQty) h
        split
        · refine ⟨_, pop _ _ h1, hp1, ?_, ?_, ?_, rfl⟩
          · have : (L1.orders.tail.map (·.id)).Sublist (L1.orders.map (·.id)) := by
              cases L1.orders <;> simp
            rw [← hi1]; exact this
          · simp only [popHead, setHeadRem, own_frame]
          · simp [popHead, setHeadRem]
        · exact ⟨L1, h1, hp1, hi1 ▸ List.Sublist.refl _, by simp only [setHeadRem, own_frame],
            by simp [setHeadRem], rfl⟩
      · cases hs

-- ============================================================================
-- The inner loop
-- ============================================================================

section Loops

variable {c : Ctx} {o1 : Order} {own : List PriceLevel} {tm : Nat}

/-- **The inner loop.** From a walk state at head level `L :: R` whose price
    crosses, the inner loop keeps the reference's remaining computation. It
    leaves `R` alone; if the match is not over, the head level is empty and
    the reference's contra side is `R`; if it is over, the two contra sides
    agree up to the view. -/
theorem inner_sim (hco : CO c o1) : ∀ (n : Nat) (st st' : State) (inc : Order) (L : PriceLevel)
    (R : List PriceLevel),
    innerRun c n st = some st' → sideL st.book c.contra = L :: R →
    canMatchPrice o1 L.price = true → (∀ o ∈ L.orders, Good o) → IR o1 st inc →
    ∃ inc' cref' L',
      MatcherSpec.rest inc own (normC (L :: R)) st.trades tm =
        MatcherSpec.rest inc' own cref' st'.trades tm ∧
      IR o1 st' inc' ∧ sideL st'.book c.contra = L' :: R ∧ L'.price = L.price ∧
      (0 < st'.rem → L'.orders = [] ∧ cref' = R) ∧
      (st'.rem = 0 → cref'.map nL = (normC (L' :: R)).map nL) ∧
      (L'.orders.map (·.id)).Sublist (L.orders.map (·.id)) ∧
      st'.stop = st.stop ∧ sideL st'.book c.own = sideL st.book c.own ∧
      st'.book.stops = st.book.stops := by
  intro n
  induction n with
  | zero =>
    intro st st' inc L R hrun h hpr hg hir
    unfold innerRun at hrun
    split at hrun
    · cases hrun
    · rename_i ht
      simp only [Option.some.injEq] at hrun; subst hrun
      refine ⟨inc, normC (L :: R), L, rfl, hir, h, rfl, fun h0 => ?_, fun _ => rfl,
        List.Sublist.refl _, rfl, rfl, rfl⟩
      have hL : L.orders = [] := by
        simp only [innerTest, tBest_eq, h, List.head?_cons, Option.bind_some, qFirst,
          Bool.and_eq_true, decide_eq_true_eq, not_and] at ht
        cases hq : L.orders with
        | nil => rfl
        | cons _ _ => simp [hq] at ht; exact absurd ht (Nat.pos_iff_ne_zero.mp h0)
      exact ⟨hL, normC_cons_nil hL⟩
  | succ n ih =>
    intro st st' inc L R hrun h hpr hg hir
    unfold innerRun at hrun
    split at hrun
    · rename_i ht
      have hrem : 0 < st.rem := by simp [innerTest] at ht; exact ht.2
      cases hq : L.orders with
      | nil => simp [innerTest, tBest_eq, h, qFirst, hq] at ht
      | cons p os =>
        cases hs : innerStep c st with
        | none => rw [hs] at hrun; cases hrun
        | some st1 =>
          rw [hs] at hrun
          simp only [Option.bind_some] at hrun
          obtain ⟨inc1, cref1, L1, hir1, hre1, h1, hp1, hcase, hstop1, hown1, hstops1⟩ :=
            step_sim (own := own) (tm := tm) hco hs h hq (hg p (by rw [hq]; exact List.mem_cons_self))
              hpr hir hrem
          obtain ⟨L1', h1', -, hsub1, -, -, -⟩ := innerStep_frame h hs
          have hLL : L1' = L1 := by rw [h1] at h1'; exact (List.cons.inj h1').1.symm
          rw [hLL, hq] at hsub1
          rw [normC_cons_ne (by simp [hq])]
          rcases hcase with ⟨ho1, hc1⟩ | ⟨hr1, hv1⟩
          · obtain ⟨inc', cref', L', hre, hir', h', hp', hpos, hzero, hsub, hstop, hown, hstops⟩ :=
              ih st1 st' inc1 L1 R hrun h1 (by rw [hp1]; exact hpr)
                (fun o ho => hg o (by rw [hq, ← ho1] at *; exact List.mem_cons_of_mem _ ho)) hir1
            rw [hc1] at hre1
            exact ⟨inc', cref', L', hre1.trans hre, hir', h', hp'.trans hp1, hpos, hzero,
              hsub.trans hsub1, hstop.trans hstop1, hown.trans hown1, hstops.trans hstops1⟩
          · have hex : innerRun c n st1 = some st1 := innerRun_exit (by simp [innerTest, hr1]) n
            rw [hex] at hrun
            simp only [Option.some.injEq] at hrun; subst hrun
            exact ⟨inc1, cref1, L1, hre1, hir1, h1, hp1, fun h0 => absurd hr1 (Nat.pos_iff_ne_zero.mp h0),
              fun _ => hv1, hsub1, hstop1, hown1, hstops1⟩
    · rename_i ht
      simp only [Option.some.injEq] at hrun; subst hrun
      refine ⟨inc, normC (L :: R), L, rfl, hir, h, rfl, fun h0 => ?_, fun _ => rfl,
        List.Sublist.refl _, rfl, rfl, rfl⟩
      have hL : L.orders = [] := by
        simp only [innerTest, tBest_eq, h, List.head?_cons, Option.bind_some, qFirst,
          Bool.and_eq_true, decide_eq_true_eq, not_and] at ht
        cases hq : L.orders with
        | nil => rfl
        | cons _ _ => simp [hq] at ht; exact absurd ht (Nat.pos_iff_ne_zero.mp h0)
      exact ⟨hL, normC_cons_nil hL⟩

end Loops

-- ============================================================================
-- The outer loop
-- ============================================================================

def NonE (L : List PriceLevel) : Prop := ∀ l ∈ L, l.orders ≠ []
def GoodL (L : List PriceLevel) : Prop := ∀ l ∈ L, ∀ o ∈ l.orders, Good o

theorem outerRun_final {c : Ctx} : ∀ {n : Nat} {st st' : State},
    outerRun c n st = some st' → outerTest st' = false
  | 0, st, st', h => by
    unfold outerRun at h
    split at h
    · cases h
    · rename_i hnt; simp only [Option.some.injEq] at h; subst h; exact Bool.eq_false_iff.mpr hnt
  | n + 1, st, st', h => by
    unfold outerRun at h
    split at h
    · cases hs : outerStep c st with
      | none => rw [hs] at h; cases h
      | some s1 => rw [hs] at h; exact outerRun_final h
    · rename_i hnt; simp only [Option.some.injEq] at h; subst h; exact Bool.eq_false_iff.mpr hnt

section Outer

variable {c : Ctx} {o1 : Order} {own : List PriceLevel} {tm : Nat}

/-- The outer loop's invariant: the walk's own side and stops are the input's;
    the contra side's ids only shrink; while quantity remains the contra side
    has no empty level and only good orders; and the reference's final result
    `Rf` is the remaining computation from the reference state related to the
    walk's (while the loop runs), or its terminal state (once it has exited). -/
structure OW (c : Ctx) (o1 : Order) (own : List PriceLevel) (tm : Nat) (ids0 : List Nat)
    (Rf : MatchResult) (st : State) : Prop where
  ownEq : sideL st.book c.own = own
  stops : st.book.stops = []
  sub   : (ids (sideL st.book c.contra)).Sublist ids0
  live  : 0 < st.rem → NonE (sideL st.book c.contra) ∧ GoodL (sideL st.book c.contra)
  rel   : ∃ inc cref, IR o1 st inc ∧
    (outerTest st = true → cref = sideL st.book c.contra ∧
      Rf = MatcherSpec.rest inc own cref st.trades tm) ∧
    (outerTest st = false → Rf = term inc own cref st.trades tm ∧
      cref.map nL = (sideL st.book c.contra).map nL)

theorem IR.sameRem {o1 inc : Order} {st st' : State} (h : IR o1 st inc) (e : st'.rem = st.rem) :
    IR o1 st' inc := ⟨h.shape, fun h0 => h.zero (e ▸ h0), fun h0 => e ▸ h.pos (e ▸ h0)⟩

theorem ids_sub_of_head {L L' : PriceLevel} {R : List PriceLevel}
    (h : (L'.orders.map (·.id)).Sublist (L.orders.map (·.id))) :
    (ids (L' :: R)).Sublist (ids (L :: R)) := by
  rw [ids_cons, ids_cons]; exact h.append (List.Sublist.refl _)

/-- One outer iteration keeps `OW`. -/
theorem outerStep_OW (hco : CO c o1) (hb : c.bound = some (c.cap + 1)) {ids0 : List Nat}
    {Rf : MatchResult} {st st1 : State} (hw : OW c o1 own tm ids0 Rf st)
    (ht : outerTest st = true) (hs : outerStep c st = some st1) : OW c o1 own tm ids0 Rf st1 := by
  have hrem : 0 < st.rem := by simp [outerTest] at ht; exact ht.1
  have hstp : st.stop = false := by simp [outerTest] at ht; exact ht.2
  obtain ⟨inc, cref, hir, hrun, -⟩ := hw.rel
  obtain ⟨hcref, hRf⟩ := hrun ht
  obtain ⟨hne, hgd⟩ := hw.live hrem
  have stopState : ∀ (hterm : MatcherSpec.rest inc own (sideL st.book c.contra) st.trades tm =
      term inc own (sideL st.book c.contra) st.trades tm),
      OW c o1 own tm ids0 Rf { st with stop := true } := by
    intro hterm
    refine ⟨hw.ownEq, hw.stops, hw.sub, fun _ => ⟨hne, hgd⟩, inc, cref, hir.sameRem rfl,
      fun h => by simp [outerTest] at h, fun _ => ⟨?_, by rw [hcref]⟩⟩
    rw [hRf, hcref, hterm]
  unfold outerStep at hs
  rw [tBest_eq] at hs
  cases h : sideL st.book c.contra with
  | nil =>
    rw [h] at hs; simp only [List.head?_nil, Option.some.injEq] at hs; subst hs
    apply stopState
    rw [h]; exact rest_empty (hir.notDone hrem)
  | cons L R =>
    rw [h] at hs
    simp only [List.head?_cons] at hs
    by_cases hpc : c.r.orderType ≠ 1 ∧ ¬c.crosses L.price = true
    · rw [if_pos hpc] at hs; simp only [Option.some.injEq] at hs; subst hs
      apply stopState
      rw [h]
      have : canMatchPrice inc L.price = false := by
        cases e : canMatchPrice inc L.price
        · rfl
        · rcases (canMatch_iff hco hir.shape L.price).mp e with e1 | e1
          · exact absurd e1 hpc.1
          · exact absurd e1 hpc.2
      exact rest_noprice (hir.notDone hrem) this
    · rw [if_neg hpc, hb] at hs
      simp only [Option.bind_eq_bind, Option.bind_some] at hs
      have hcan : canMatchPrice o1 L.price = true := by
        rw [canMatch_iff hco (IncShape.refl o1)]
        by_cases e : c.r.orderType = 1
        · exact Or.inl e
        · exact Or.inr (by simpa [e] using hpc)
      have hLne : L.orders ≠ [] := hne L (by rw [h]; exact List.mem_cons_self)
      cases hin : innerRun c (c.cap + 1) st with
      | none => rw [hin] at hs; cases hs
      | some s1 =>
        rw [hin] at hs
        simp only [Option.bind_some] at hs
        obtain ⟨inc', cref', L', hre, hir', h', -, hpos, hzero, hsub, hstop, hown, hstops⟩ :=
          inner_sim (own := own) (tm := tm) hco (c.cap + 1) st s1 inc L R hin h hcan
            (fun o ho => hgd L (by rw [h]; exact List.mem_cons_self) o ho) hir
        rw [normC_cons_ne hLne] at hre
        rw [tBest_eq, h', List.head?_cons] at hs
        simp only at hs
        have hsubR : (ids R).Sublist ids0 := by
          have := hw.sub; rw [h, ids_cons] at this; exact (List.sublist_append_right _ _).trans this
        have hsubL' : (ids (L' :: R)).Sublist ids0 := (ids_sub_of_head hsub).trans (h ▸ hw.sub)
        by_cases hr : 0 < s1.rem
        · obtain ⟨hL'e, hcr⟩ := hpos hr
          rw [if_pos (by simp [levelCount, hL'e])] at hs
          simp only [Option.some.injEq] at hs; subst hs
          have hc1 : sideL (dropBest s1.book c.contra) c.contra = R := by simp [h']
          have ht1 : outerTest { s1 with book := dropBest s1.book c.contra } = true := by
            simp [outerTest, hr, hstop, hstp]
          refine ⟨?_, ?_, ?_, fun _ => ⟨?_, ?_⟩, inc', R, hir'.sameRem rfl, fun _ => ⟨hc1.symm, ?_⟩,
            fun hf => by rw [ht1] at hf; cases hf⟩
          · simp only [dropBest, own_frame]; rw [hown, hw.ownEq]
          · simp [dropBest, hstops, hw.stops]
          · rw [hc1]; exact hsubR
          · rw [hc1]; intro l hl; exact hne l (by rw [h]; exact List.mem_cons_of_mem _ hl)
          · rw [hc1]; intro l hl; exact hgd l (by rw [h]; exact List.mem_cons_of_mem _ hl)
          · rw [hRf, hcref, h, hre, hcr]
        · have hr0 : s1.rem = 0 := Nat.eq_zero_of_not_pos hr
          have hdone : done inc' = true := hir'.zero hr0
          have hnorm : ∀ bk : BookState, sideL bk c.contra = normC (L' :: R) →
              OW c o1 own tm ids0 Rf { s1 with book := bk } → True := fun _ _ _ => trivial
          clear hnorm
          have key : ∀ (bk : BookState), sideL bk c.contra = normC (L' :: R) →
              sideL bk c.own = own → bk.stops = [] →
              OW c o1 own tm ids0 Rf { s1 with book := bk } := by
            intro bk hbk hbo hbs
            refine ⟨hbo, hbs, ?_, fun h0 => absurd hr0 (Nat.pos_iff_ne_zero.mp h0), inc', cref',
              hir'.sameRem rfl, fun h1 => by simp [outerTest, hr0] at h1, fun _ => ⟨?_, ?_⟩⟩
            · rw [hbk]
              refine List.Sublist.trans ?_ hsubL'
              by_cases he : L'.orders = []
              · rw [normC_cons_nil he, ids_cons, he]; simp
              · rw [normC_cons_ne he]; exact List.Sublist.refl _
            · rw [hRf, hcref, h, hre]; exact rest_done hdone
            · rw [hbk]; exact hzero hr0
          by_cases hz : levelCount L' = 0
          · rw [if_pos hz] at hs; simp only [Option.some.injEq] at hs; subst hs
            have hL'e : L'.orders = [] := List.eq_nil_of_length_eq_zero hz
            refine key _ (by simp [h', normC_cons_nil hL'e]) ?_ ?_
            · simp only [dropBest, own_frame]; rw [hown, hw.ownEq]
            · simp [dropBest, hstops, hw.stops]
          · rw [if_neg hz] at hs; simp only [Option.some.injEq] at hs; subst hs
            have hL'e : L'.orders ≠ [] := fun e => hz (by simp [levelCount, e])
            refine key s1.book (by rw [h', normC_cons_ne hL'e]) (by rw [hown, hw.ownEq])
              (by rw [hstops, hw.stops])

/-- **The outer loop.** `OW` holds throughout, and at exit the reference's
    result is a terminal state related to the walk's. -/
theorem outer_sim (hco : CO c o1) (hb : c.bound = some (c.cap + 1)) {ids0 : List Nat}
    {Rf : MatchResult} : ∀ (n : Nat) (st st' : State),
    outerRun c n st = some st' → OW c o1 own tm ids0 Rf st → OW c o1 own tm ids0 Rf st' := by
  intro n
  induction n with
  | zero =>
    intro st st' hrun hw
    unfold outerRun at hrun
    split at hrun
    · cases hrun
    · simp only [Option.some.injEq] at hrun; subst hrun; exact hw
  | succ n ih =>
    intro st st' hrun hw
    unfold outerRun at hrun
    split at hrun
    · rename_i ht
      cases hs : outerStep c st with
      | none => rw [hs] at hrun; cases hrun
      | some st1 =>
        rw [hs] at hrun
        exact ih st1 st' hrun (outerStep_OW hco hb hw ht hs)
    · simp only [Option.some.injEq] at hrun; subst hrun; exact hw

end Outer

end Walk
