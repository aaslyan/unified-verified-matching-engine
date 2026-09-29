import Matcher.Rest

/-!
# Phase 4: an accepted order refines `processB`, and the main theorem

`side_run` runs `gen_process_buy` / `gen_process_sell` on a request that passed
the entry checks: the post-only check, `rem := qty`, the matching loop
(`outer_loop`), the resting step (`rest_run`) and the result code. It matches
`processWithId` through `processWithId_match` / `processWithId_postOnly` and
`postOnly_reject_agrees`.

`matcher_refines`: for every store satisfying `Inv` and every request, the
matcher refines `processB` (plan v2 §2).
-/

namespace MatcherAccept

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherCancel
  MatcherStore MatcherLoop MatcherSpec MatcherInner MatcherOuter MatcherRest

-- ============================================================================
-- The spec order of a request
-- ============================================================================

/-- The fields of `r.toSpec`. -/
structure SpecOrd (r : CRequest) (o : Order) : Prop where
  id : o.id = r.id.toNat
  side : o.side = if r.side = 0 then .buy else .sell
  price : o.price = if r.orderType = 1 then none else some r.price.toNat
  ty : o.orderType = if r.orderType = 1 then .market else .limit
  tif : o.tif = if r.orderType = 1 ∨ r.orderType = 2 then .ioc else .gtc
  po : o.postOnly = decide (r.orderType = 3)
  qty : o.qty = r.qty.toNat
  rem : o.remainingQty = r.qty.toNat
  minq : o.minQty = none
  disp : o.displayQty = none
  stop : o.stopPrice = none
  st : o.status = .new_
  group : o.stpGroup = stpGroupOf r.account
  policy : o.stpPolicy = stpPolicyOf r.account r.stpMode

theorem specOrd_of {r : CRequest} {o : Order} (h : r.toSpec = some o) : SpecOrd r o := by
  unfold CRequest.toSpec at h
  split at h
  · rename_i sd ot md hs hot hm
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        have hs' : sd = if r.side = 0 then .buy else .sell := by
          unfold decodeSide at hs
          have e : r.side = 0 ↔ r.side.toNat = 0 := by rw [← UInt8.toNat_inj]; rfl
          split at hs <;> simp_all
        have ht : ∀ k : UInt8, r.orderType = k ↔ r.orderType.toNat = k.toNat := fun k => by
          rw [← UInt8.toNat_inj]
        have hot' : (ot = .limit ↔ r.orderType = 0) ∧ (ot = .market ↔ r.orderType = 1) ∧
            (ot = .ioc ↔ r.orderType = 2) ∧ (ot = .postOnly ↔ r.orderType = 3) := by
          rw [ht 0, ht 1, ht 2, ht 3]
          unfold decodeOrderType at hot
          split at hot <;> simp_all <;> (try subst hot) <;> simp
        obtain ⟨h0, h1, h2, h3⟩ := hot'
        refine ⟨rfl, hs', ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
          cases ot <;> simp_all [CRequest.mkOrder, COrderType.specPrice, COrderType.specType,
            COrderType.tif, COrderType.isPostOnly]
  · cases h

-- ============================================================================
-- The spec run of an accepted order, as the remaining computation
-- ============================================================================

theorem sideOf_isBuy {isBuy : Bool} {r : CRequest} (hb : isBuy = decide (r.side = 0)) :
    (if r.side = 0 then Side.buy else Side.sell) = if isBuy then .buy else .sell := by
  subst hb; by_cases h : r.side = 0 <;> simp [h]

theorem mr_rest {db : Db} {o : Order} {isBuy : Bool}
    (hside : o.side = if isBuy then .buy else .sell) :
    mrOf (absBook db) o = rest (o1Of (absBook db) o) (absSide db (ownT isBuy))
      (absSide db (contraT isBuy)) [] ((absBook db).clock + 1) := by
  have hgt := computeMatchFuel_gt_matchMeasure (absBook db) (o1Of (absBook db) o) o.side
  unfold mrOf
  cases isBuy <;> simp only [Bool.false_eq_true, if_false, if_true] at hside
  · have : contraLevels (absBook db) o.side = absSide db (contraT false) := by
      rw [hside]; rfl
    rw [this] at hgt
    rw [← rest_start (own := absSide db (ownT false)) (trades := []) (tm := (absBook db).clock + 1) hgt]
    unfold dm
    rw [show (o1Of (absBook db) o).side = o.side from rfl, hside]; rfl
  · have : contraLevels (absBook db) o.side = absSide db (contraT true) := by
      rw [hside]; rfl
    rw [this] at hgt
    rw [← rest_start (own := absSide db (ownT true)) (trades := []) (tm := (absBook db).clock + 1) hgt]
    unfold dm
    rw [show (o1Of (absBook db) o).side = o.side from rfl, hside]; rfl

theorem term_bids_asks (inc : Order) (own contra : List PriceLevel) (trades : List Trade)
    (tm : Timestamp) (isBuy : Bool) (hs : inc.side = if isBuy then .buy else .sell) :
    ((term inc own contra trades tm).bids = if isBuy then own else contra) ∧
    ((term inc own contra trades tm).asks = if isBuy then contra else own) := by
  unfold term; cases isBuy <;> simp at hs <;> simp [hs, bidsOf, asksOf]

/-- The decoded book when nothing rests: it is the matching run's book. -/
theorem book_norest {db : Db} {own contra : List PriceLevel} {isBuy : Bool} {B : BookState}
    (hown : absSide db (ownT isBuy) = own)
    (hcv : (absSide db (contraT isBuy)).map levelView = contra.map levelView)
    (hb : B.bids = if isBuy then own else contra) (ha : B.asks = if isBuy then contra else own)
    (hs : B.stops = []) : bookView (absBook db) = bookView B := by
  simp only [bookView, absBook, BookView.mk.injEq, hb, ha, hs, List.map_nil, and_true]
  cases isBuy
  · simp only [ownT, contraT, Bool.false_eq_true, if_false] at hown hcv ⊢
    rw [hown, hcv]; simp
  · simp only [ownT, contraT, if_true] at hown hcv ⊢
    rw [hown, hcv]; simp

/-- The order `insertOrder` rests. -/
def restOrd (inc : Order) (hasT : Bool) : Order :=
  { inc with visibleQty := inc.remainingQty, status := if hasT then .partiallyFilled else .new_,
             minQty := none }

/-- The decoded book when the remainder rests: the own side gets the spec's
    insertion. -/
theorem book_rest {db1 db2 : Db} {own contra : List PriceLevel} {isBuy : Bool} {A : BookState}
    {inc : Order} {hasT : Bool} {p : Nat}
    (hown : absSide db1 (ownT isBuy) = own)
    (hcv : (absSide db1 (contraT isBuy)).map levelView = contra.map levelView)
    (hRB : (absSide db2 (ownT isBuy)).map levelView =
        (insSpec (ownT isBuy) (absSide db1 (ownT isBuy)) (restOrd inc hasT) p).map levelView ∧
      absSide db2 (contraT isBuy) = absSide db1 (contraT isBuy))
    (hb : A.bids = if isBuy then own else contra) (ha : A.asks = if isBuy then contra else own)
    (hs : A.stops = []) (hside : inc.side = if isBuy then .buy else .sell)
    (hdisp : inc.displayQty = none) (hp : inc.price.getD 0 = p) :
    bookView (absBook db2) = bookView (insertOrder A inc hasT) := by
  obtain ⟨h1, h2⟩ := hRB
  obtain ⟨iid, isd, ity, itif, ipx, istop, iq, irem, imq, idq, ivq, ipo, ist, its, ig, ipol⟩ := inc
  simp only at hside hdisp hp
  subst hdisp hp
  unfold insertOrder
  cases isBuy
  · simp only [Bool.false_eq_true, if_false] at hside hb ha
    subst hside
    simp only [ownT, contraT, Bool.false_eq_true, if_false] at hown hcv h1 h2
    simp only [bookView, absBook, BookView.mk.injEq, hs, List.map_nil, and_true]
    refine ⟨?_, ?_⟩
    · rw [h2, hcv, hb]
    · rw [h1, hown, ha]; rfl
  · simp only [if_true] at hside hb ha
    subst hside
    simp only [ownT, contraT, if_true] at hown hcv h1 h2
    simp only [bookView, absBook, BookView.mk.injEq, hs, List.map_nil, and_true]
    refine ⟨?_, ?_⟩
    · rw [h1, hown, hb]; rfl
    · rw [h2, hcv, ha]

-- ============================================================================
-- Request facts after the entry checks
-- ============================================================================

structure Static (r : CRequest) : Prop where
  ty : r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3
  side : r.side = 0 ∨ r.side = 1
  stp : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4
  qty : r.qty ≠ 0
  price : r.orderType ≠ 1 → r.price ≠ 0

theorem static_of {cap : Nat} {r : CRequest} (h : staticCode cap r = none) : Static r := by
  unfold staticCode at h
  have h1 : r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3 := by
    by_cases x : r.orderType = 0 ∨ r.orderType = 1 ∨ r.orderType = 2 ∨ r.orderType = 3
    · exact x
    · rw [if_pos x] at h; cases h
  rw [if_neg (fun x => x h1)] at h
  have h2 : r.side = 0 ∨ r.side = 1 := by
    by_cases x : r.side = 0 ∨ r.side = 1
    · exact x
    · rw [if_pos x] at h; cases h
  rw [if_neg (fun x => x h2)] at h
  have h3 : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4 := by
    by_cases x : r.stpMode = 0 ∨ r.stpMode = 1 ∨ r.stpMode = 2 ∨ r.stpMode = 3 ∨ r.stpMode = 4
    · exact x
    · rw [if_pos x] at h; cases h
  rw [if_neg (fun x => x h3)] at h
  have h4 : r.qty ≠ 0 := fun x => by rw [if_pos x] at h; cases h
  rw [if_neg h4] at h
  have h5 : ¬(r.orderType ≠ 1 ∧ r.price = 0) := fun x => by rw [if_pos x] at h; cases h
  exact ⟨h1, h2, h3, h4, fun a b => h5 ⟨a, b⟩⟩

theorem dispose_rest {inc : Order} {A : BookState} {tr : List Trade}
    (hnd : (inc.remainingQty == 0 || inc.status == .cancelled) = false) (htif : inc.tif = .gtc)
    (hty : inc.orderType = .limit) : dispose inc A tr = insertOrder A inc (!tr.isEmpty) := by
  unfold dispose
  have h1 : (TimeInForce.gtc == TimeInForce.ioc) = false := by decide
  have h2 : (OrderType.limit == OrderType.market) = false := by decide
  simp [hnd, htif, hty, h1, h2]

theorem dispose_norest {inc : Order} {A : BookState} {tr : List Trade}
    (h : (inc.remainingQty == 0 || inc.status == .cancelled) = true ∨ inc.tif = .ioc) :
    dispose inc A tr = A := by
  unfold dispose
  rcases h with h | h
  · simp [h]
  · have h1 : (TimeInForce.ioc == TimeInForce.ioc) = true := by decide
    split
    · rfl
    · simp [h, h1]

theorem restOrd_view {r : CRequest} {o : Order} {b : BookState} {inc : Order} {isBuy : Bool}
    {rem : UInt64} (hsd : SpecOrd r o) (hbuy : isBuy = decide (r.side = 0))
    (hty : r.orderType = 0 ∨ r.orderType = 3) (hs : IncShape (o1Of b o) inc)
    (hrem : inc.remainingQty = rem.toNat) (hasT : Bool) (n : Nat) :
    orderView (restOrd inc hasT) = orderView (restingOrder (ownT isBuy) (r.restRow rem) n) := by
  have hn1 : r.orderType ≠ 1 := by rcases hty with h | h <;> rw [h] <;> decide
  have hn2 : ¬(r.orderType = 1 ∨ r.orderType = 2) := by
    rcases hty with h | h <;> rw [h] <;> decide
  have hside : sideOfTree (ownT isBuy) = if r.side = 0 then .buy else .sell := by
    subst hbuy; by_cases h : r.side = 0 <;> simp [h, ownT, sideOfTree]
  rw [hs]
  simp only [restOrd, orderView, restingOrder, o1Of, CRequest.restRow, OrderView.mk.injEq]
  rw [hsd.id, hsd.side, hside, hsd.ty, if_neg hn1, hsd.tif, if_neg hn2, hsd.price, if_neg hn1,
    hsd.stop, hsd.qty, hsd.disp, hsd.group, hsd.policy, hrem]
  simp

-- ============================================================================
-- The post-only check
-- ============================================================================

section PO

variable {S : Type} [EngineDb S]

open EngineDb

variable {s : S} {r : CRequest} {L : Loc} {ts : List TradeObs}

theorem ev_poCond_none (isBuy : Bool) (hb : L.best = none) :
    evalExpr (mkSt s r L ts) (and' (not' (.isNullL (v "best"))) (crossesE isBuy (.getL (v "best") .price))) =
      .ok (.bool false) := by
  lsimp [hb]

theorem ev_poCond_some (isBuy : Bool) {l : LevelH} {lrow : LevelRow} (hb : L.best = some l)
    (hl : liveL (view s) l = true) (hrl : readLevel s l = some lrow) :
    evalExpr (mkSt s r L ts) (and' (not' (.isNullL (v "best"))) (crossesE isBuy (.getL (v "best") .price))) =
      .ok (.bool (decide (crossB isBuy lrow.price r.price))) := by
  cases isBuy
  · by_cases hc : r.price ≤ lrow.price <;> (simp only [crossesE]; lsimp [hb, hl, hrl, hc, crossB])
  · by_cases hc : lrow.price ≤ r.price <;> (simp only [crossesE]; lsimp [hb, hl, hrl, hc, crossB])

theorem ev_po_skip (isBuy : Bool) (h3 : r.orderType ≠ 3) :
    Eval program (poStmt isBuy) (mkSt s r L ts) (mkSt s r L ts, .normal) :=
  Eval.when_false (by lsimp [h3])

/-- The best contra price the post-only check sees, and the spec's `wouldCross`. -/
theorem wouldCross_iff {isBuy : Bool} {o : Order} (hw : (view s).WF) (hsd : SpecOrd r o)
    (hbuy : isBuy = decide (r.side = 0)) (_hs01 : r.side = 0 ∨ r.side = 1) (h3 : r.orderType = 3) :
    (tBest s (contraT isBuy) = none → wouldCross o (absBook (view s)) = false) ∧
    (∀ l lrow, tBest s (contraT isBuy) = some l → readLevel s l = some lrow →
      wouldCross o (absBook (view s)) = decide (crossB isBuy lrow.price r.price)) := by
  have hpx : o.price = some r.price.toNat := by rw [hsd.price, if_neg (by rw [h3]; decide)]
  have hsd' : o.side = if isBuy then .buy else .sell := by rw [hsd.side, sideOf_isBuy hbuy]
  have hlaw := tBest_law s (contraT isBuy) hw
  constructor
  · intro hn
    rw [hn] at hlaw
    have : absSide (view s) (contraT isBuy) = [] := by
      simp only [absSide, show (view s).tree (contraT isBuy) = [] from hlaw]; rfl
    unfold wouldCross bestAskPrice bestBidPrice
    rw [hpx]
    cases isBuy <;> simp only [Bool.false_eq_true, if_false, if_true] at hsd' <;> rw [hsd'] <;>
      simp only [absBook] <;> simp only [contraT, Bool.false_eq_true, if_false, if_true] at this <;>
      simp [this]
  · intro l lrow hb hrl
    rw [hb] at hlaw
    obtain ⟨hl, hlb⟩ := hlaw
    have hsplit := absSide_best hw hl hlb
    have hlp : (view s).levelPrice l = lrow.price := by
      rw [readLevel_law] at hrl; simp [Db.levelPrice, hrl]
    unfold wouldCross bestAskPrice bestBidPrice
    rw [hpx]
    cases isBuy <;> simp only [Bool.false_eq_true, if_false, if_true] at hsd' <;> rw [hsd'] <;>
      simp only [absBook] <;> simp only [contraT, Bool.false_eq_true, if_false, if_true] at hsplit <;>
      rw [hsplit] <;> simp [absLevel, hlp, crossB, UInt64.le_iff_toNat_le]

end PO

-- ============================================================================
-- The side function
-- ============================================================================

section Side

variable {S : Type} [EngineDb S]

open EngineDb

/-- After the post-only check: `rem := qty`, the matching loop, the resting
    step and `return ACCEPTED` refine `doMatch` and `dispose`. -/
theorem side_cont {s : S} {r : CRequest} {o : Order} (hcap : CapOk S) (hI : Inv s)
    (hst : Static r) (hsd : SpecOrd r o) (hdup : hashFind s r.id = none)
    (hnf : ¬ ((r.orderType = 0 ∨ r.orderType = 3) ∧ capacity (S := S) ≤ count s))
    (isBuy : Bool) (hbuy : isBuy = decide (r.side = 0)) (L0 : Loc) (hst0 : L0.stop = false) :
    ∃ st1, Eval program (Stmt.block [.assign "rem" (v "qty"), outerLoop isBuy, restStmt isBuy,
        retc .accepted]) (mkSt s r L0 []) (st1, .ret (.code (codeOf .accepted))) ∧
      st1.trades = (mrOf (absBook (view s)) o).trades.map tradeObs ∧
      bookView (absBook (view st1.store)) =
        bookView (dispose (mrOf (absBook (view s)) o).incoming (afterMatch (absBook (view s)) o)
          (mrOf (absBook (view s)) o).trades) ∧
      Inv st1.store := by
  have hw := hI.wf
  have hside : o.side = if isBuy then .buy else .sell := by rw [hsd.side, sideOf_isBuy hbuy]
  let b := absBook (view s)
  let o1 := o1Of b o
  let own := absSide (view s) (ownT isBuy)
  let contra0 := absSide (view s) (contraT isBuy)
  let c : MCtx := ⟨r, isBuy, o1, own, b.clock + 1, mrOf b o, count s⟩
  have hc : c.Ok := ⟨⟨hsd.id, hsd.group, hsd.policy, hst.stp⟩, hside, hsd.price⟩
  have hC0 : c.C0 ≤ capacity (S := S) := hI.count_le
  have hmr : c.mr = rest o1 own contra0 [] (b.clock + 1) := mr_rest hside
  have hhash : ∀ h ∈ (view s).hash, (view s).orderId h ≠ r.id := by
    have := hashFind_law s r.id hw; rw [hdup] at this; exact this
  let L1 : Loc := { L0 with rem := r.qty }
  have e1 : Eval program (.assign "rem" (v "qty")) (mkSt s r L0 []) (mkSt s r L1 [], .normal) :=
    ev_assign (by lsimp) (set_rem r L0 r.qty)
  have hO : OInv c s L1 [] o1 contra0 [] := by
    refine ⟨hI, rfl, hmr, rfl, ?_, IncShape.refl _, rfl, ?_, Nat.le_refl _, hhash, UInt64.le_refl _,
      fun h => by simp [L1, hst0] at h, fun h => by simp [L1, hst0] at h⟩
    · show r.qty.toNat = _
      have : o1.status ≠ .cancelled := by simp [o1, o1Of, hsd.st]
      rw [if_neg this]; simp [o1, o1Of, hsd.rem]
    · show 0 + count s ≤ count s + _; omega
  obtain ⟨s1, L2, ts1, inc1, contra1, strades1, eloop, hO1, hexit, hterm⟩ := outer_loop hc hcap hC0 hO
  have hmr' : mrOf b o = term inc1 own contra1 strades1 (b.clock + 1) := hterm
  have hinc1side : inc1.side = if isBuy then .buy else .sell := by rw [hO1.shape.side]; exact hside
  obtain ⟨hbids, hasks⟩ := term_bids_asks inc1 own contra1 strades1 (b.clock + 1) isBuy hinc1side
  have hA_b : (afterMatch b o).bids = if isBuy then own else contra1 := by
    show (mrOf b o).bids = _; rw [hmr']; exact hbids
  have hA_a : (afterMatch b o).asks = if isBuy then contra1 else own := by
    show (mrOf b o).asks = _; rw [hmr']; exact hasks
  have hA_s : (afterMatch b o).stops = [] := rfl
  have htr : (mrOf b o).trades = strades1 := by rw [hmr']; rfl
  have hic : (mrOf b o).incoming = inc1 := by rw [hmr']; rfl
  have e3tail : ∀ {st : St S}, Eval program (retc .accepted) st (st, .ret (.code (codeOf .accepted))) :=
    fun {st} => Eval.retcode (st := st) .accepted
  by_cases hrest : L2.rem ≠ 0 ∧ r.orderType ≠ 2 ∧ r.orderType ≠ 1
  · obtain ⟨hr0, hi, hm⟩ := hrest
    have hty03 : r.orderType = 0 ∨ r.orderType = 3 := by
      rcases hst.ty with h | h | h | h
      · exact Or.inl h
      · exact absurd h hm
      · exact absurd h hi
      · exact Or.inr h
    have hcnt1 : count s1 < capacity (S := S) := by
      have h1c : count s1 ≤ count s := hO1.cnt
      have : count s < capacity (S := S) := by
        by_cases h : capacity (S := S) ≤ count s
        · exact absurd ⟨hty03, h⟩ hnf
        · omega
      omega
    obtain ⟨s3, L3, h, hf, hRV, hw3, hc3, erest⟩ :=
      rest_run (r := r) (L := L2) (ts := ts1) isBuy hO1.inv hcnt1 hO1.hashid hr0 hi hm
    have hstop : L2.stop = true := by
      rcases hexit with h | h
      · exact absurd h hr0
      · exact h
    have hnd := notDone_of hO1.aggr hr0
    have hremN : inc1.remainingQty = L2.rem.toNat := by
      have hagg := hO1.aggr
      have hnc : inc1.status ≠ .cancelled := by
        intro e; rw [if_pos e] at hagg; exact hr0 (UInt64.toNat_inj.mp (by rw [hagg]; rfl))
      rw [if_neg hnc] at hagg; exact hagg.symm
    have hov := restOrd_view (b := b) (isBuy := isBuy) (rem := L2.rem) hsd hbuy hty03 hO1.shape hremN
      (!strades1.isEmpty)
    refine ⟨mkSt s3 r L3 ts1, Eval.block_cons_normal e1 (Eval.block_cons_normal eloop
      (Eval.block_cons_normal erest e3tail (by simp)) (by simp)) (by simp), ?_, ?_, ?_⟩
    · show ts1 = _; rw [htr]; exact hO1.trades
    · have hn1 : r.orderType ≠ 1 := hm
      have hn12 : ¬(r.orderType = 1 ∨ r.orderType = 2) := fun h => by
        rcases h with h | h; exact hm h; exact hi h
      have htif : inc1.tif = .gtc := by
        rw [hO1.shape]; show o.tif = _; rw [hsd.tif, if_neg hn12]
      have hty : inc1.orderType = .limit := by
        rw [hO1.shape]; show o.orderType = _; rw [hsd.ty, if_neg hn1]
      rw [hic, htr, dispose_rest hnd htif hty]
      refine book_rest (db1 := view s1) hO1.own hO1.cview
        (rest_book hO1.inv.wf hf hRV hov) hA_b hA_a hA_s hinc1side ?_ ?_
      · rw [hO1.shape]; exact hsd.disp
      · rw [hO1.shape]; show (o.price).getD 0 = _; rw [hsd.price, if_neg hn1]; rfl
    · refine rest_inv hO1.inv hcnt1 hf hRV hw3 hc3 ?_ rfl ?_ hO1.remle ?_ ?_ ?_
      · show r.side = sideCode (ownT isBuy)
        subst hbuy; rcases hst.side with h | h <;> simp [h, ownT, sideCode]
      · exact pos_of_ne hr0
      · show r.stpMode ≤ 4
        rcases hst.stp with h | h | h | h | h <;> rw [h] <;> decide
      · exact pos_of_ne (hst.price hm)
      · intro y hy
        have hx : ¬ crossB isBuy ((view s1).levelPrice y) r.price := hO1.stopX hstop hm y hy
        cases isBuy <;> simp only [crossB, Bool.false_eq_true, if_false, if_true] at hx ⊢ <;>
          rw [UInt64.le_iff_toNat_le] at hx <;> rw [UInt64.lt_iff_toNat_lt] <;> omega
  · have ernr : Eval program (restStmt isBuy) (mkSt s1 r L2 ts1) (mkSt s1 r L2 ts1, .normal) := by
      refine Eval.when_false (ev_restCond_false ?_)
      by_cases h0 : L2.rem = 0
      · exact Or.inl h0
      · by_cases h2 : r.orderType = 2
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Classical.byContradiction fun h1 => hrest ⟨h0, h2, h1⟩))
    refine ⟨mkSt s1 r L2 ts1, Eval.block_cons_normal e1 (Eval.block_cons_normal eloop
      (Eval.block_cons_normal ernr e3tail (by simp)) (by simp)) (by simp), ?_, ?_, hO1.inv⟩
    · show ts1 = _; rw [htr]; exact hO1.trades
    · rw [hic, htr]
      rw [dispose_norest ?_]
      · exact book_norest hO1.own hO1.cview hA_b hA_a hA_s
      · by_cases h0 : L2.rem = 0
        · exact Or.inl (done_of hO1.aggr h0)
        · right
          have h12 : r.orderType = 1 ∨ r.orderType = 2 := by
            by_cases h2 : r.orderType = 2
            · exact Or.inr h2
            · exact Or.inl (Classical.byContradiction fun h1 => hrest ⟨h0, h2, h1⟩)
          rw [hO1.shape]; show o.tif = _; rw [hsd.tif, if_pos h12]

theorem wouldCross_o1 (b : BookState) (o : Order) :
    wouldCross (o1Of b o) { b with nextId := o.id } = wouldCross o b := rfl

/-- **The side function** refines the spec step of an order that passed the entry
    checks: `processWithId`, with `postOnlyCode` as the result code. -/
theorem side_run {s : S} {r : CRequest} {o : Order} (hcap : CapOk S) (hI : Inv s)
    (hts : r.toSpec = some o) (hsc : staticCode (capacity (S := S)) r = none)
    (hdup : hashFind s r.id = none)
    (hnf : ¬ ((r.orderType = 0 ∨ r.orderType = 3) ∧ capacity (S := S) ≤ count s))
    (isBuy : Bool) (hbuy : isBuy = decide (r.side = 0)) :
    ∃ st1 k, Eval program (sideFun isBuy).body (mkSt s r {} []) (st1, .ret (.code k)) ∧
      k = codeOf (postOnlyCode o (absBook (view s))) ∧
      st1.trades = (processWithId (absBook (view s)) o).trades.map tradeObs ∧
      bookView (absBook (view st1.store)) = bookView (processWithId (absBook (view s)) o).book ∧
      Inv st1.store := by
  have hst := static_of hsc
  have hsd := specOrd_of hts
  have hw := hI.wf
  have hns := toSpec_not_stop hts
  rw [sideFun_body]
  have hstops : (absBook (view s)).stops = [] := rfl
  by_cases h3 : r.orderType = 3
  · have hpo : o.postOnly = true := by rw [hsd.po, h3]; rfl
    have hn1 : r.orderType ≠ 1 := by rw [h3]; decide
    have hn12 : ¬(r.orderType = 1 ∨ r.orderType = 2) := by rw [h3]; decide
    obtain ⟨wc_none, wc_some⟩ := wouldCross_iff (isBuy := isBuy) hw hsd hbuy hst.side h3
    have e_tb := ev_tBest (P := program) (s := s) (r := r) (L := ({} : Loc)) (ts := []) (contraT isBuy)
    have eq3 : evalExpr (mkSt s r ({} : Loc) []) (eqc "otype" OT_POST_ONLY) = .ok (.bool true) := by
      lsimp [h3]
    -- the order does not cross: it goes on to the matching loop (which makes no step)
    have noncross : wouldCross o (absBook (view s)) = false →
        Eval program (poStmt isBuy) (mkSt s r {} [])
          (mkSt s r { ({} : Loc) with best := tBest s (contraT isBuy) } [], .normal) →
        ∃ st1 k, Eval program (Stmt.block [poStmt isBuy, .assign "rem" (v "qty"), outerLoop isBuy,
          restStmt isBuy, retc .accepted]) (mkSt s r {} []) (st1, .ret (.code k)) ∧
          k = codeOf (postOnlyCode o (absBook (view s))) ∧
          st1.trades = (processWithId (absBook (view s)) o).trades.map tradeObs ∧
          bookView (absBook (view st1.store)) = bookView (processWithId (absBook (view s)) o).book ∧
          Inv st1.store := by
      intro hwc epo
      obtain ⟨st1, ecnt, htr, hbk, hinv⟩ := side_cont hcap hI hst hsd hdup hnf isBuy hbuy
        { ({} : Loc) with best := tBest s (contraT isBuy) } rfl
      obtain ⟨ht, hb⟩ := processWithId_postOnly hstops hns hpo (by rw [wouldCross_o1]; exact hwc)
        (by rw [hsd.rem]; intro e; exact hst.qty (UInt64.toNat_inj.mp (by rw [e]; rfl)))
        hsd.st (by rw [hsd.tif, if_neg hn12]) (by rw [hsd.ty, if_neg hn1])
        ⟨_, by rw [hsd.price, if_neg hn1]⟩
      refine ⟨st1, _, Eval.block_cons_normal epo ecnt (by simp), ?_, ?_, ?_, hinv⟩
      · simp [postOnlyCode, hpo, hwc]
      · rw [htr, ht]
      · rw [hbk, hb]
    cases hb : tBest s (contraT isBuy) with
    | none =>
      apply noncross (wc_none hb)
      rw [hb] at e_tb
      have ew : Eval program (Stmt.block [whenS (and' (not' (.isNullL (v "best")))
          (crossesE isBuy (.getL (v "best") .price))) (retc .rejectedPostOnly)])
          (mkSt s r { ({} : Loc) with best := none } []) (mkSt s r { ({} : Loc) with best := none } [], .normal) :=
        Eval.when_false (ev_poCond_none (s := s) (r := r) (L := { ({} : Loc) with best := none }) (ts := []) isBuy rfl)
      rw [hb]
      exact Eval.when_true eq3 (Eval.block_cons_normal e_tb ew (by simp))
    | some l =>
      have hlaw := tBest_law s (contraT isBuy) hw
      rw [hb] at hlaw e_tb
      have hll : liveL (view s) l = true := hw.tree_live _ _ hlaw.1
      obtain ⟨lrow, hlrow⟩ : ∃ lrow, readLevel s l = some lrow := by
        rw [readLevel_law]; simp only [liveL] at hll; exact Option.isSome_iff_exists.mp hll
      have hwc := wc_some l lrow hb hlrow
      have econd := ev_poCond_some (s := s) (r := r) (L := { ({} : Loc) with best := some l }) (ts := [])
        isBuy rfl hll hlrow
      by_cases hcx : crossB isBuy lrow.price r.price
      · -- it crosses: rejected, nothing changes
        have hwc' : wouldCross o (absBook (view s)) = true := by rw [hwc]; simp [hcx]
        have hcode : postOnlyCode o (absBook (view s)) = .rejectedPostOnly := by
          simp [postOnlyCode, hpo, hwc']
        obtain ⟨ht, hb1, ha1, hs1⟩ := postOnly_reject_agrees hns hcode
        refine ⟨mkSt s r { ({} : Loc) with best := some l } [], _, ?_, by rw [hcode], ?_, ?_, hI⟩
        · refine Eval.block_cons_ret (Eval.when_true eq3 (Eval.block_cons_normal e_tb
            (Eval.block_cons_ret (Eval.when_true (by rw [econd, decide_eq_true hcx])
              (Eval.retcode .rejectedPostOnly))) (by simp)))
        · show [] = _; rw [ht]; rfl
        · simp only [bookView, hb1, ha1, hs1]; rfl
      · apply noncross (by rw [hwc]; simp [hcx])
        have ew : Eval program (Stmt.block [whenS (and' (not' (.isNullL (v "best")))
            (crossesE isBuy (.getL (v "best") .price))) (retc .rejectedPostOnly)])
            (mkSt s r { ({} : Loc) with best := some l } []) (mkSt s r { ({} : Loc) with best := some l } [], .normal) :=
          Eval.when_false (by rw [econd, decide_eq_false hcx])
        rw [hb]
        exact Eval.when_true eq3 (Eval.block_cons_normal e_tb ew (by simp))
  · have hpo : o.postOnly = false := by rw [hsd.po]; simp [h3]
    obtain ⟨st1, ecnt, htr, hbk, hinv⟩ := side_cont hcap hI hst hsd hdup hnf isBuy hbuy {} rfl
    have hfok : o.tif ≠ .fok := by rw [hsd.tif]; split <;> decide
    have hmtl : o.orderType ≠ .marketToLimit := by rw [hsd.ty]; split <;> decide
    obtain ⟨ht, hb⟩ := processWithId_match hstops hns hfok hsd.minq hmtl hpo
    refine ⟨st1, _, Eval.block_cons_normal (ev_po_skip isBuy h3) ecnt (by simp), ?_, ?_, ?_, hinv⟩
    · simp [postOnlyCode, hpo]
    · rw [htr, ht]
    · rw [hbk, hb]

end Side

-- ============================================================================
-- The entry function: dispatch to the side function
-- ============================================================================

section Entry

variable {S : Type} [EngineDb S]

open EngineDb

def dupEnvR (r : CRequest) (x : Option OrderH) (k : UInt8) : List (Ident × Val) :=
  [("id", .u64 r.id), ("account", .u64 r.account), ("side", .code r.side),
   ("otype", .code r.orderType), ("stp", .code r.stpMode), ("price", .u64 r.price),
   ("qty", .u64 r.qty), ("dup", .order x), ("r", .code k)]

theorem lookup_side (isBuy : Bool) :
    lookupFun program (if isBuy then "gen_process_buy" else "gen_process_sell") = .ok (sideFun isBuy) := by
  cases isBuy <;> simp (config := {decide := true}) [lookupFun, program, List.find?, minFun, sideFun,
    processOrderFun, cancelOrderFun]

theorem ev_call_side {s : S} {r : CRequest} (isBuy : Bool) {st1 : St S} {k : UInt8}
    (hbody : Eval program (sideFun isBuy).body (mkSt s r {} []) (st1, .ret (.code k))) :
    Eval program (.call (some "r") (if isBuy then "gen_process_buy" else "gen_process_sell")
        [v "id", v "account", v "side", v "otype", v "stp", v "price", v "qty"]) (dupSt s r)
      ({ st1 with env := dupEnvR r (hashFind s r.id) k }, .normal) := by
  refine Eval.call (lookup_side isBuy) (st₁ := st1) (v := .code k)
    (env := dupEnvR r (hashFind s r.id) k)
    (vals := [.u64 r.id, .u64 r.account, .code r.side, .code r.orderType, .code r.stpMode,
      .u64 r.price, .u64 r.qty])
    (penv := [("id", .u64 r.id), ("account", .u64 r.account), ("side", .code r.side),
      ("otype", .code r.orderType), ("stp", .code r.stpMode), ("price", .u64 r.price), ("qty", .u64 r.qty)])
    (by simp (config := {decide := true}) [dupSt, dupEnv, v, evalExpr, lookupVar, List.lookup,
      List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure])
    (by cases isBuy <;> simp [bindParams, sideFun, Val.ty, Functor.map, Except.map]) ?_
    (by cases isBuy <;> rfl)
    (by simp (config := {decide := true}) [bindResult, setVar, dupSt, dupEnv, dupEnvR, List.lookup, Val.ty])
  have : ({ dupSt s r with env := [("id", .u64 r.id), ("account", .u64 r.account), ("side", .code r.side),
      ("otype", .code r.orderType), ("stp", .code r.stpMode), ("price", .u64 r.price), ("qty", .u64 r.qty)] ++
      (sideFun isBuy).locals.map fun (x, t) => (x, t.default) } : St S) = mkSt s r {} [] := by
    cases isBuy <;> simp [dupSt, mkSt, sEnv, sideFun, Ty.default]
  rw [this]; exact hbody

/-- **An accepted order refines `processB`.** -/
theorem refines_accept {s : S} {r : CRequest} (hI : Inv s) (hcap : CapOk S)
    (hn : staticCode (capacity (S := S)) r = none) (hd : ¬(hashFind s r.id).isSome = true)
    (hnf : ¬((r.orderType = 0 ∨ r.orderType = 3) ∧ capacity (S := S) ≤ count s)) :
    Refines s (.order r) := by
  obtain ⟨o, hts, hid, hspec⟩ := processB_after_static (b := absBook (view s)) hn
  have hbook : ¬ idOnBook (absBook (view s)) o.id = true := by
    rw [hid]; exact fun h => hd ((hashFind_isSome_iff hI r.id).mpr h)
  have hmay : ¬ (requestMayRest r && decide (capacity (S := S) ≤ bookSize (absBook (view s)))) = true := by
    rw [bookSize_absBook, ← hI.count_eq]
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact hnf ⟨requestMayRest_iff.mp h.1, h.2⟩
  have hsp : specStep s (.order r) = (postOnlyCode o (absBook (view s)), processWithId (absBook (view s)) o) := by
    unfold specStep; rw [hspec, if_neg hbook, if_neg hmay]
  have hdn : hashFind s r.id = none := by
    cases h : hashFind s r.id
    · rfl
    · rw [h] at hd; exact absurd rfl hd
  let isBuy := decide (r.side = 0)
  obtain ⟨st1, k, ebody, hk, htr, hbk, hinv⟩ := side_run hcap hI hts hn hdn hnf isBuy rfl
  have hst := static_of hn
  have ecall := ev_call_side (s := s) (r := r) isBuy ebody
  have eite : Eval program (.ite (eqc "side" SIDE_BUY)
      (.call (some "r") "gen_process_buy" [v "id", v "account", v "side", v "otype", v "stp", v "price", v "qty"])
      (.call (some "r") "gen_process_sell" [v "id", v "account", v "side", v "otype", v "stp", v "price", v "qty"]))
      (dupSt s r) ({ st1 with env := dupEnvR r (hashFind s r.id) k }, .normal) := by
    by_cases h0 : r.side = 0
    · have hb : isBuy = true := by simp [isBuy, h0]
      rw [hb] at ecall
      exact Eval.ite_true (by simp (config := {decide := true}) [dupSt, dupEnv, eqc, b2, v, c, evalExpr,
        lookupVar, List.lookup, evalBin, h0, SIDE_BUY, bind, Except.bind]) ecall
    · have hb : isBuy = false := by simp [isBuy, h0]
      rw [hb] at ecall
      exact Eval.ite_false (by simp (config := {decide := true}) [dupSt, dupEnv, eqc, b2, v, c, evalExpr,
        lookupVar, List.lookup, evalBin, h0, SIDE_BUY, bind, Except.bind]) ecall
  have eret : Eval program (.ret (v "r")) ({ st1 with env := dupEnvR r (hashFind s r.id) k } : St S)
      ({ st1 with env := dupEnvR r (hashFind s r.id) k }, .ret (.code k)) :=
    Eval.ret (by simp (config := {decide := true}) [dupEnvR, v, evalExpr, lookupVar, List.lookup])
  have hbody : Eval program (Stmt.block (processOrderStmts.drop 6)) (orderSt s r)
      ({ st1 with env := dupEnvR r (hashFind s r.id) k }, .ret (.code k)) := by
    simp only [processOrderStmts, List.drop]
    exact Eval.block_cons_normal (eval_dup s r)
      (Eval.block_cons_normal (Eval.when_pass (ev_dupcheck s r) hd)
        (Eval.block_cons_normal (Eval.when_pass (ev_capcheck s r hcap hI.count_le) hnf)
          (Eval.block_cons_normal eite eret (by simp)) (by simp)) (by simp)) (by simp)
  obtain ⟨f, hrun⟩ := order_run ((prefix_run hcap s r).2 hn _ hbody)
  refine ⟨f, st1.store, st1.trades, ?_, ?_, ?_, hinv⟩
  · rw [hsp, ← hk]; exact hrun
  · rw [hsp]; exact htr
  · rw [hsp]; exact hbk

end Entry

-- ============================================================================
-- The main theorem
-- ============================================================================

/-- **The generated matcher refines `processB`** (plan v2 §2): for every store
    whose view satisfies `Inv`, and every request, running the matcher program
    ends without error and reports the result code, trades and book view that
    `processB (capacity) (absBook (view s)) req` reports, and `Inv` holds again.
    Standing hypothesis: `capacity + 1 < 2^64` (`CapOk`). -/
theorem matcher_refines {S : Type} [EngineDb S] (hcap : CapOk S) {s : S} (hI : Inv s) (req : Req) :
    Refines s req := by
  cases req with
  | cancel id => exact MatcherCancel.refines_cancel id hI hcap
  | order r =>
    cases hsc : staticCode (EngineDb.capacity (S := S)) r with
    | some c => exact refines_static hI hcap hsc
    | none =>
      by_cases hd : (EngineDb.hashFind s r.id).isSome = true
      · exact refines_duplicate hI hcap hsc hd
      · by_cases hf : (r.orderType = 0 ∨ r.orderType = 3) ∧ EngineDb.capacity (S := S) ≤ EngineDb.count s
        · exact refines_capacity hI hcap hsc hd hf
        · exact refines_accept hI hcap hsc hd hf

/-- The invariant holds on the initial store, so `matcher_refines` applies to
    every request of every trace, one step at a time. -/
theorem inv_init {S : Type} [EngineDb S] : Inv (EngineDb.init : S) := by
  have hv := EngineDb.init_view (S := S)
  refine ⟨by rw [hv]; exact WF_empty, by rw [hv]; exact ClientInv_empty, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; rw [hv]; simp [Db.orderLive, Db.queued, Db.empty]
  · intro l; rw [hv]; simp [Db.levelLive, Db.empty]
  · rw [EngineDb.init_count, hv]; rfl
  · rw [EngineDb.init_levelsUsed, hv]; rfl
  · rw [EngineDb.init_count]; exact Nat.zero_le _

end MatcherAccept
