import Walk.EquivMatch

/-!
# A2: `Walk.process` means what `processB` means

**`process_obs_eq`**: on a book satisfying `WF` (every book the C can hold),
the walking spec does not trap, and its observation — result code, trades as
`TradeObs`, book view — is `processB`'s. The stronger `process_agree` gives
the trades as reference `Trade`s, element for element, and the books equal up
to `nB` (the view as a spec object).

Assembly: entry checks and cancel (`EquivEntry`), the post-only decision, the
matching loop (`outer_sim`, from `step_sim` via `inner_sim`), and the rest
block against `dispose`, whose three failure returns are dead on a `WF` book.
-/

namespace Walk

open EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherSpec MatcherInner MatcherRun
  MatcherRest MatcherAccept

-- ============================================================================
-- Books through the view, by side
-- ============================================================================

theorem nB_eq_of_sides {c : Ctx} {X Y : BookState}
    (ho : (sideL X c.own).map nL = (sideL Y c.own).map nL)
    (hc : (sideL X c.contra).map nL = (sideL Y c.contra).map nL)
    (hs : X.stops.map nO = Y.stops.map nO) : nB X = nB Y := by
  obtain ⟨cap, r, isBuy⟩ := c
  cases isBuy <;> simp_all [nB, sideL, Ctx.own, Ctx.contra]

theorem allIds (c : Ctx) (b : BookState) :
    ((allBookOrders b).map (·.id)).Perm (ids (sideL b c.own) ++ ids (sideL b c.contra)) := by
  unfold Ctx.own Ctx.contra
  cases c.isBuy
  · simp only [Bool.false_eq_true, if_false, allBookOrders, List.map_append, ids, sideL]
    exact List.perm_append_comm
  · simp only [if_true, allBookOrders, List.map_append, ids, sideL]
    exact List.Perm.refl _

theorem count_sides (c : Ctx) (b : BookState) :
    count b = (ids (sideL b c.own)).length + (ids (sideL b c.contra)).length := by
  have := (allIds c b).length_eq
  simp only [List.length_map, List.length_append] at this
  exact this

theorem levelsUsed_sides (c : Ctx) (b : BookState) :
    levelsUsed b = (sideL b c.own).length + (sideL b c.contra).length := by
  unfold levelsUsed Ctx.own Ctx.contra
  cases c.isBuy <;> simp [sideL] <;> omega

theorem hashFind_none_of {c : Ctx} {b : BookState} {n : Nat}
    (h : n ∉ ids (sideL b c.own) ∧ n ∉ ids (sideL b c.contra)) : (hashFind b n).isSome = false := by
  rw [hashFind_isSome]
  cases e : idOnBook b n
  · rfl
  · exfalso
    simp only [idOnBook, List.any_eq_true, beq_iff_eq] at e
    obtain ⟨o, ho, hon⟩ := e
    have := (allIds c b).subset (List.mem_map_of_mem (f := (·.id)) ho)
    rw [hon] at this
    rcases List.mem_append.mp this with h1 | h1
    · exact h.1 h1
    · exact h.2 h1

theorem length_le_ids {L : List PriceLevel} (h : NonE L) : L.length ≤ (ids L).length := by
  rw [← sideCount_eq_ids]; exact length_le_sideCount h

-- ============================================================================
-- Resting the remainder
-- ============================================================================

/-- On a side with distinct prices, `modAt` changes the one level at `p`. -/
theorem modAt_eq_map {t : Tree} {p : Nat} {f : PriceLevel → PriceLevel} :
    ∀ {L : List PriceLevel}, L.Pairwise (fun x y => prioB t x.price y.price = true) →
      modAt p f L = L.map (fun y => if y.price = p then f y else y)
  | [], _ => rfl
  | y :: ys, hs => by
    rw [List.pairwise_cons] at hs
    by_cases hy : y.price = p
    · have hrest : ∀ z ∈ ys, z.price ≠ p := by
        intro z hz e
        have := hs.1 z hz
        rw [hy, e] at this
        cases t <;> simp [prioB] at this
      simp only [modAt, hy, if_true, List.map_cons]
      congr 1
      exact ((List.map_congr_left fun z hz => by simp [hrest z hz]).trans (List.map_id ys)).symm
    · simp only [modAt, hy, if_false, List.map_cons]
      rw [modAt_eq_map hs.2]

/-- A fresh level, then an append at its price, is a fresh level with the order. -/
theorem modAt_insLevel {t : Tree} {p : Nat} {f : PriceLevel → PriceLevel}
    (hf : ∀ y, (f y).price = y.price) : ∀ {L : List PriceLevel}, (∀ y ∈ L, y.price ≠ p) →
      modAt p f (insLevel t { price := p, orders := [] } L) = insLevel t (f { price := p, orders := [] }) L
  | [], _ => by simp [insLevel, modAt]
  | y :: ys, h => by
    have hy : y.price ≠ p := h y List.mem_cons_self
    simp only [insLevel, hf]
    split
    · simp [modAt]
    · simp only [modAt, hy, if_false]
      rw [modAt_insLevel hf (fun z hz => h z (List.mem_cons_of_mem _ hz))]

/-- The order the walk rests and the order `insertOrder` rests have the same view. -/
theorem nO_restOrder {c : Ctx} {o : Order} {b : BookState} {inc : Order}
    (hsd : SpecOrd c.r o) (hty : c.r.orderType = 0 ∨ c.r.orderType = 3)
    (hs : IncShape (o1Of b o) inc) (rem : Nat) (hrem : inc.remainingQty = rem) (hasT : Bool) :
    nO (restOrder c rem) = nO (restOrd inc hasT) := by
  have hn1 : c.r.orderType ≠ 1 := by rcases hty with h | h <;> rw [h] <;> decide
  have hn2 : ¬(c.r.orderType = 1 ∨ c.r.orderType = 2) := by
    rcases hty with h | h <;> rw [h] <;> decide
  rw [hs]
  simp only [nO, restOrder, restOrd, o1Of, Order.mk.injEq]
  have hn2' : c.r.orderType ≠ 2 := fun h => hn2 (Or.inr h)
  simp [hsd.id, hsd.side, hsd.ty, hn1, hn2', hsd.tif, hsd.price, hsd.stop, hsd.qty, hsd.disp,
    hsd.group, hsd.policy, hrem]

theorem sideL_insertOrder {c : Ctx} {A : BookState} {inc : Order} {hasT : Bool}
    (hside : inc.side = if c.isBuy then .buy else .sell) (hdisp : inc.displayQty = none) :
    sideL (insertOrder A inc hasT) c.own = insSpec c.own (sideL A c.own) (restOrd inc hasT) (inc.price.getD 0) ∧
    sideL (insertOrder A inc hasT) c.contra = sideL A c.contra ∧
    (insertOrder A inc hasT).stops = A.stops := by
  unfold insertOrder restOrd Ctx.own Ctx.contra
  rw [hdisp]
  cases hb : c.isBuy <;> simp only [hb, Bool.false_eq_true, if_false, if_true] at hside ⊢ <;>
    rw [hside] <;> exact ⟨rfl, rfl, rfl⟩

/-- The rest block when the remainder rests and no failure branch fires. -/
theorem rest_found {c : Ctx} {st : State} {lv : PriceLevel}
    (hr : 0 < st.rem) (h2 : c.r.orderType ≠ 2) (h1 : c.r.orderType ≠ 1)
    (hcnt : ¬ c.cap ≤ count st.book) (hdup : (hashFind st.book c.r.id.toNat).isSome = false)
    (hf : tFind st.book c.own c.r.price.toNat = some lv) :
    rest c st = (.accepted, qInsertTail st.book c.own c.r.price.toNat (restOrder c st.rem)) := by
  unfold rest
  rw [if_pos ⟨hr, h2, h1⟩, if_neg hcnt]
  simp only [hf, hdup, Bool.false_eq_true, if_false]

theorem rest_fresh {c : Ctx} {st : State}
    (hr : 0 < st.rem) (h2 : c.r.orderType ≠ 2) (h1 : c.r.orderType ≠ 1)
    (hcnt : ¬ c.cap ≤ count st.book) (hlev : ¬ c.cap ≤ levelsUsed st.book)
    (hdup : (hashFind st.book c.r.id.toNat).isSome = false)
    (hf : tFind st.book c.own c.r.price.toNat = none) :
    rest c st = (.accepted, qInsertTail (tInsertNew st.book c.own c.r.price.toNat) c.own
      c.r.price.toNat (restOrder c st.rem)) := by
  unfold rest
  rw [if_pos ⟨hr, h2, h1⟩, if_neg hcnt]
  simp only [hf, hlev, hdup, Bool.false_eq_true, if_false]

theorem rest_none {c : Ctx} {st : State} (h : ¬ (0 < st.rem ∧ c.r.orderType ≠ 2 ∧ c.r.orderType ≠ 1)) :
    rest c st = (.accepted, st.book) := by
  unfold rest; rw [if_neg h]

-- ============================================================================
-- The side function
-- ============================================================================

/-- The request's spec order, as `CO` states it. -/
theorem CO_of {c : Ctx} {o : Order} {b : BookState} (hsd : SpecOrd c.r o) (hst : Static c.r)
    (hcb : c.isBuy = decide (c.r.side = 0)) : CO c (o1Of b o) :=
  { side := by show o.side = _; rw [hsd.side]; exact sideOf_isBuy hcb
    price := hsd.price
    id := hsd.id
    po := hsd.po
    group := hsd.group
    policy := hsd.policy
    stp := hst.stp }

/-- `mrOf` as the reference's remaining computation, own and contra side by `Ctx`. -/
theorem mr_eq {c : Ctx} {b : BookState} {o : Order} (hside : o.side = if c.isBuy then .buy else .sell) :
    mrOf b o = MatcherSpec.rest (o1Of b o) (sideL b c.own) (sideL b c.contra) [] (b.clock + 1) := by
  have hgt := computeMatchFuel_gt_matchMeasure b (o1Of b o) o.side
  have hcl : contraLevels b o.side = sideL b c.contra := by
    unfold Ctx.contra; rw [hside]; cases c.isBuy <;> rfl
  rw [hcl] at hgt
  unfold mrOf
  rw [← rest_start (own := sideL b c.own) (trades := []) (tm := b.clock + 1) hgt]
  unfold dm Ctx.own Ctx.contra
  rw [show (o1Of b o).side = o.side from rfl, hside]
  cases c.isBuy <;> rfl

/-- The walk's post-only test is `postOnlyCode`'s. -/
theorem postOnly_iff {c : Ctx} {o : Order} {b : BookState}
    (hsd : SpecOrd c.r o) (hbuy : c.isBuy = decide (c.r.side = 0)) :
    (c.r.orderType = 3 ∧ postOnlyCross c b = true) ↔ postOnlyCode o b = .rejectedPostOnly := by
  unfold postOnlyCode wouldCross postOnlyCross
  rw [hsd.po, hsd.price, hsd.side, sideOf_isBuy hbuy]
  by_cases h3 : c.r.orderType = 3
  · have hn1 : c.r.orderType ≠ 1 := by rw [h3]; decide
    rw [if_neg hn1]
    simp only [h3, decide_true, Bool.true_and, true_and]
    unfold tBest Ctx.contra Ctx.crosses bestAskPrice bestBidPrice
    cases c.isBuy
    · simp only [Bool.false_eq_true, if_false, sideL]
      cases b.bids <;> simp
    · simp only [if_true, sideL]
      cases b.asks <;> simp [ge_iff_le]
  · simp [h3]

/-- **The side function**: once the entry checks pass, the walk's matching
    phase agrees with `processWithId`. -/
theorem sideProc_agree {c : Ctx} {b : BookState} {o : Order} (hw : WF c.cap b)
    (hto : c.r.toSpec = some o) (hst : Static c.r) (hbuy : c.isBuy = decide (c.r.side = 0))
    (hid : idOnBook b o.id = false)
    (hcap : ¬ (requestMayRest c.r = true ∧ c.cap ≤ bookSize b)) :
    ∃ w, sideProc c b = some w ∧ Agree w (postOnlyCode o b, processWithId b o) := by
  have hsd := specOrd_of hto
  have hside : o.side = if c.isBuy then .buy else .sell := by rw [hsd.side]; exact sideOf_isBuy hbuy
  have hco : CO c (o1Of b o) := CO_of hsd hst hbuy
  have hb : c.bound = some (c.cap + 1) := by simp [Ctx.bound, hw.cap64]
  have pwi := pwi_cases hto hw.stops
  -- dead branches of the rest block need these
  have hty_of : c.r.orderType ≠ 2 → c.r.orderType ≠ 1 → c.r.orderType = 0 ∨ c.r.orderType = 3 := by
    intro h2 h1
    rcases hst.ty with h | h | h | h
    · exact Or.inl h
    · exact absurd h h1
    · exact absurd h h2
    · exact Or.inr h
  have hlt_of : c.r.orderType = 0 ∨ c.r.orderType = 3 → count b < c.cap := by
    intro hty
    have hmr' : requestMayRest c.r = true := requestMayRest_iff.mpr hty
    rw [count_eq_bookSize hw.stops]
    exact Nat.lt_of_not_le (fun hh => hcap ⟨hmr', hh⟩)
  unfold sideProc
  simp only
  by_cases hpo : c.r.orderType = 3 ∧ postOnlyCross c b = true
  · -- post-only, crossing: rejected with the book unchanged
    rw [if_pos hpo]
    have hrej := (postOnly_iff hsd hbuy).mp hpo
    obtain ⟨ht, hv⟩ := pwi.1 hrej
    exact ⟨_, rfl, by rw [hrej], by rw [ht], hv.symm⟩
  · rw [if_neg hpo]
    have hacc : postOnlyCode o b = .accepted := by
      rcases postOnlyCode_cases o b with e | e
      · exact absurd ((postOnly_iff hsd hbuy).mpr e) hpo
      · exact e
    obtain ⟨ht, hv⟩ := pwi.2 hacc
    rw [hb]
    simp only [Option.bind_eq_bind, Option.bind_some]
    -- the matching loop
    have hq0 : 0 < c.r.qty.toNat := by
      have := hst.qty
      exact Nat.pos_of_ne_zero (fun e => this (UInt64.toNat_inj.mp (by simpa using e)))
    have hne : ∀ t, NonE (sideL b t) := hw.nonempty
    have hgd : ∀ t, GoodL (sideL b t) := fun t l hl o' ho' =>
      ⟨(hw.resting t l hl o' ho').1, (hw.resting t l hl o' ho').2.1, (hw.resting t l hl o' ho').2.2.1⟩
    obtain ⟨st, hst'⟩ := Option.isSome_iff_exists.mp
      (outerRun_ok (c := c) hb (c.cap + 1)
        { book := b, rem := c.r.qty.toNat, stop := false, trades := [] }
        (Nat.lt_succ_of_le (Nat.le_trans (length_le_sideCount (hw.nonempty c.contra))
          (Nat.le_trans (sideCount_le_count b c.contra) hw.count)))
        (fun _ => by simpa [pot, contraCount] using
          Nat.le_trans (sideCount_le_count b c.contra) hw.count))
    rw [hst']
    simp only [Option.bind_some]
    have hw0 : OW c (o1Of b o) (sideL b c.own) (b.clock + 1) (ids (sideL b c.contra)) (mrOf b o)
        { book := b, rem := c.r.qty.toNat, stop := false, trades := [] } := by
      refine ⟨rfl, hw.stops, List.Sublist.refl _, fun _ => ⟨hne _, hgd _⟩, o1Of b o, sideL b c.contra,
        ⟨IncShape.refl _, fun h0 => absurd h0 (Nat.pos_iff_ne_zero.mp hq0),
          fun _ => ⟨hsd.rem, by show o.status ≠ _; rw [hsd.st]; decide⟩⟩,
        fun _ => ⟨rfl, mr_eq hside⟩, fun hf => ?_⟩
      simp [outerTest, hq0] at hf
    have hwf := outer_sim hco hb (c.cap + 1) _ st hst' hw0
    have hfin := outerRun_final hst'
    obtain ⟨inc, cref, hir, -, hterm⟩ := hwf.rel
    obtain ⟨hmr, hcv⟩ := hterm hfin
    -- the reference's book after matching
    have hincside : inc.side = if c.isBuy then .buy else .sell := by rw [hir.shape.side]; exact hside
    have hba := term_bids_asks inc (sideL b c.own) cref st.trades (b.clock + 1) c.isBuy hincside
    have hAown : sideL (afterMatch b o) c.own = sideL b c.own := by
      have e : sideL (afterMatch b o) c.own = if c.isBuy then (mrOf b o).bids else (mrOf b o).asks := by
        unfold afterMatch Ctx.own; cases c.isBuy <;> rfl
      rw [e, hmr, hba.1, hba.2]; cases c.isBuy <;> rfl
    have hAcon : sideL (afterMatch b o) c.contra = cref := by
      have e : sideL (afterMatch b o) c.contra = if c.isBuy then (mrOf b o).asks else (mrOf b o).bids := by
        unfold afterMatch Ctx.contra; cases c.isBuy <;> rfl
      rw [e, hmr, hba.1, hba.2]; cases c.isBuy <;> rfl
    have hAstops : (afterMatch b o).stops = [] := by simp [afterMatch, hw.stops]
    have hmrtr : (mrOf b o).trades = st.trades := by rw [hmr]; rfl
    have hmrinc : (mrOf b o).incoming = inc := by rw [hmr]; rfl
    have hcnt_of : c.r.orderType = 0 ∨ c.r.orderType = 3 → ¬ c.cap ≤ count st.book := by
      intro hty
      have hlt := hlt_of hty
      rw [count_sides c st.book, hwf.ownEq]
      rw [count_sides c b] at hlt
      have := hwf.sub.length_le
      omega
    have hdup_of : (hashFind st.book c.r.id.toNat).isSome = false := by
      apply hashFind_none_of (c := c)
      have hid' : c.r.id.toNat ∉ (allBookOrders b).map (·.id) := by
        intro hm
        rw [← hsd.id] at hm
        simp only [idOnBook, List.any_eq_false, beq_iff_eq] at hid
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
        exact hid x hx hxe
      have hb' := fun hm => hid' ((allIds c b).symm.subset (List.mem_append.mpr hm))
      rw [hwf.ownEq]
      exact ⟨fun hm => hb' (Or.inl hm), fun hm => hb' (Or.inr (hwf.sub.subset hm))⟩
    have hlev_of : 0 < st.rem → c.r.orderType = 0 ∨ c.r.orderType = 3 → ¬ c.cap ≤ levelsUsed st.book := by
      intro hr hty
      have h0 := hcnt_of hty
      rw [levelsUsed_sides c st.book, hwf.ownEq]
      rw [count_sides c st.book, hwf.ownEq] at h0
      have h1' := length_le_ids (hne c.own)
      have h2' := length_le_ids (hwf.live hr).1
      omega
    -- the rest block, with its dead branches discharged
    have hrestv : ∃ bk, rest c st = (.accepted, bk) ∧
        nB bk = nB (dispose inc (afterMatch b o) st.trades) := by
      by_cases hrest : 0 < st.rem ∧ c.r.orderType ≠ 2 ∧ c.r.orderType ≠ 1
      · obtain ⟨hr, h2, h1⟩ := hrest
        have hty := hty_of h2 h1
        have hn2 : ¬(c.r.orderType = 1 ∨ c.r.orderType = 2) := fun h => by
          rcases h with h | h; exact h1 h; exact h2 h
        have hincrem : inc.remainingQty = st.rem := (hir.pos hr).1
        have hnd : (inc.remainingQty == 0 || inc.status == .cancelled) = false := hir.notDone hr
        have htif : inc.tif = .gtc := by
          rw [hir.shape]; show o.tif = _; rw [hsd.tif, if_neg hn2]
        have htyp : inc.orderType = .limit := by
          rw [hir.shape]; show o.orderType = _; rw [hsd.ty, if_neg h1]
        have hdisp : inc.displayQty = none := by rw [hir.shape]; exact hsd.disp
        have hpx : inc.price.getD 0 = c.r.price.toNat := by
          rw [hir.shape.price]; show o.price.getD 0 = _; rw [hsd.price, if_neg h1]; rfl
        rw [dispose_rest hnd htif htyp]
        obtain ⟨hio, hic, his⟩ := sideL_insertOrder (A := afterMatch b o) (hasT := !st.trades.isEmpty)
          hincside hdisp
        have hro := nO_restOrder hsd hty hir.shape st.rem hincrem (!st.trades.isEmpty)
        have hsorted := hw.sorted c.own
        rw [← hwf.ownEq] at hsorted
        have hwalk : ∀ bk : BookState, sideL bk c.contra = sideL st.book c.contra →
            sideL bk c.own = insSpec c.own (sideL st.book c.own) (restOrder c st.rem) c.r.price.toNat →
            bk.stops = [] → nB bk = nB (insertOrder (afterMatch b o) inc (!st.trades.isEmpty)) := by
          intro bk hbc hbo hbs
          apply nB_eq_of_sides (c := c)
          · rw [hbo, hio, hAown, hpx, hwf.ownEq]
            cases c.own
            · simp only [insSpec, insertDesc_nL, hro]
            · simp only [insSpec, insertAsc_nL, hro]
          · rw [hbc, hic, hAcon, hcv]
          · rw [hbs, his, hAstops]
        have happ : ∀ y : PriceLevel,
            ((fun l : PriceLevel => { l with orders := l.orders ++ [restOrder c st.rem] }) y).price = y.price :=
          fun _ => rfl
        cases hf : tFind st.book c.own c.r.price.toNat with
        | some lv =>
          refine ⟨_, rest_found hr h2 h1 (hcnt_of hty) hdup_of hf, hwalk _ ?_ ?_ ?_⟩
          · simp [qInsertTail, sideL_setSideL_ne c.own_ne.symm]
          · simp only [qInsertTail, sideL_setSideL]
            rw [modAt_eq_map hsorted]
            have hex : ∃ y ∈ sideL st.book c.own, y.price = c.r.price.toNat := by
              obtain ⟨hp1, -⟩ := List.find?_eq_some_iff_append.mp hf
              exact ⟨lv, List.mem_of_find?_eq_some hf, by simpa using hp1⟩
            rw [insSpec_exists c.own _ _ _ hsorted hex]
            rfl
          · simp [qInsertTail, hwf.stops]
        | none =>
          have hfresh : ∀ y ∈ sideL st.book c.own, y.price ≠ c.r.price.toNat := by
            intro y hy e
            unfold tFind at hf
            rw [List.find?_eq_none] at hf
            exact hf y hy (by simp [e])
          refine ⟨_, rest_fresh hr h2 h1 (hcnt_of hty) (hlev_of hr hty) hdup_of hf,
            hwalk _ ?_ ?_ ?_⟩
          · simp [qInsertTail, tInsertNew, sideL_setSideL_ne c.own_ne.symm]
          · simp only [qInsertTail, tInsertNew, sideL_setSideL]
            rw [modAt_insLevel happ hfresh, insSpec_fresh c.own _ _ _ hfresh]; rfl
          · simp [qInsertTail, tInsertNew, hwf.stops]
      · refine ⟨_, rest_none hrest, ?_⟩
        rw [dispose_norest]
        · apply nB_eq_of_sides (c := c)
          · rw [hwf.ownEq, hAown]
          · rw [hAcon, hcv]
          · rw [hwf.stops, hAstops]
        · by_cases hr : 0 < st.rem
          · right
            have h12 : c.r.orderType = 1 ∨ c.r.orderType = 2 := by
              by_cases e1 : c.r.orderType = 1
              · exact Or.inl e1
              · by_cases e2 : c.r.orderType = 2
                · exact Or.inr e2
                · exact absurd ⟨hr, e2, e1⟩ hrest
            rw [hir.shape]; show o.tif = _; rw [hsd.tif, if_pos h12]
          · left; exact hir.zero (Nat.eq_zero_of_not_pos hr)
    obtain ⟨bk, hrv, hbk⟩ := hrestv
    rw [hrv]
    refine ⟨_, rfl, by rw [hacc], by simp only; rw [ht, hmrtr], ?_⟩
    simp only
    rw [hbk, hv, hmrinc, hmrtr]

-- ============================================================================
-- The theorem
-- ============================================================================

/-- **A2.** On a `WF` book the walking spec does not trap, its result code and
    trades are `processB`'s, and its book is `processB`'s up to the view. -/
theorem process_agree {cap : Nat} {b : BookState} (hw : WF cap b) (req : Req) :
    ∃ w, process cap b req = some w ∧ Agree w (processB cap b req) := by
  cases req with
  | cancel id => exact ⟨cancel b id, rfl, by rw [cancel_eq hw id]; exact Agree.refl _⟩
  | order r =>
    rcases processOrder_entry (r := r) hw with ⟨w, hw1, hw2⟩ | ⟨o, hto, -, hid, hcap, hsc, hpo, hpb⟩
    · exact ⟨w, hw1, hw2 ▸ Agree.refl w⟩
    · obtain ⟨w, hw1, hw2⟩ := sideProc_agree (c := { cap := cap, r := r, isBuy := decide (r.side = 0) })
        hw hto (static_of hsc) rfl hid hcap
      refine ⟨w, ?_, ?_⟩
      · show processOrder cap b r = some w; rw [hpo]; exact hw1
      · rw [hpb]; exact hw2

/-- **A2, observational form** (the statement agreed at A0). -/
theorem process_obs_eq {cap : Nat} {b : BookState} (hw : WF cap b) (req : Req) :
    ∃ w, process cap b req = some w ∧ obsSpec w = obsSpec (processB cap b req) := by
  obtain ⟨w, h1, h2⟩ := process_agree hw req
  exact ⟨w, h1, h2.obs⟩

end Walk
