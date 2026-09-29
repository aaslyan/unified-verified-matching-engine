import Matcher.Accept

/-!
# The run-level theorem

`bookView` drops, of an order, `postOnly`, `status` and `timestamp`, and of the
book, `lastTradePrice`, `nextId` and `clock`. So it is not injective, and the
chain goes through `processB_congr` (route (ii)): on a book without stops, the
result code, the trades (as `TradeObs`) and the view of the new book depend
only on the view of the old book. No dropped field changes `processB`'s
behaviour on such a book: timestamps and statuses of resting orders are never
read by `doMatch`, `dispose` or `cancelOrder`; `clock` only stamps; `nextId` is
overwritten by `processWithId`; `lastTradePrice` is read only when stops
trigger, and books reached by `runB` from the empty book have no stops.

`matcher_run_refines`: for every request list, the matcher run from
`EngineDb.init` returns `.ok`, its observations equal those of `runB` from the
empty book, and `Inv` holds after every step.
-/

namespace MatcherRun

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherRefines MatcherSpec
  MatcherAccept MatcherCancel

-- ============================================================================
-- Normal forms: the view, as a spec object
-- ============================================================================

/-- An order without the fields `orderView` drops. -/
def nO (o : Order) : Order := { o with status := .new_, timestamp := 0, postOnly := false }
def nL (l : PriceLevel) : PriceLevel := { l with orders := l.orders.map nO }
/-- The incoming order: only its timestamp (the clock) differs between books. -/
def nI (o : Order) : Order := { o with timestamp := 0 }
def nR (r : MatchResult) : MatchResult :=
  { r with incoming := nI r.incoming, bids := r.bids.map nL, asks := r.asks.map nL, clock := 0 }

@[simp] theorem nO_nO (o : Order) : nO (nO o) = nO o := rfl
@[simp] theorem nL_nL (l : PriceLevel) : nL (nL l) = nL l := by
  simp [nL, Function.comp_def]
@[simp] theorem map_nL_nL (L : List PriceLevel) : (L.map nL).map nL = L.map nL := by
  simp [Function.comp_def]
@[simp] theorem nI_nI (o : Order) : nI (nI o) = nI o := rfl
@[simp] theorem nL_comp : nL ∘ nL = nL := funext nL_nL
@[simp] theorem nO_comp : nO ∘ nO = nO := rfl
@[simp] theorem nL_mk (p : Nat) (os : List Order) :
    nL { price := p, orders := os } = { price := p, orders := os.map nO } := rfl

section Fields
variable (o : Order) (l : PriceLevel)
@[simp] theorem nO_id : (nO o).id = o.id := rfl
@[simp] theorem nO_side : (nO o).side = o.side := rfl
@[simp] theorem nO_rem : (nO o).remainingQty = o.remainingQty := rfl
@[simp] theorem nO_vis : (nO o).visibleQty = o.visibleQty := rfl
@[simp] theorem nO_disp : (nO o).displayQty = o.displayQty := rfl
@[simp] theorem nO_group : (nO o).stpGroup = o.stpGroup := rfl
@[simp] theorem nI_id : (nI o).id = o.id := rfl
@[simp] theorem nI_side : (nI o).side = o.side := rfl
@[simp] theorem nI_rem : (nI o).remainingQty = o.remainingQty := rfl
@[simp] theorem nI_status : (nI o).status = o.status := rfl
@[simp] theorem nI_price : (nI o).price = o.price := rfl
@[simp] theorem nI_group : (nI o).stpGroup = o.stpGroup := rfl
@[simp] theorem nI_policy : (nI o).stpPolicy = o.stpPolicy := rfl
@[simp] theorem nI_postOnly : (nI o).postOnly = o.postOnly := rfl
@[simp] theorem nL_price : (nL l).price = l.price := rfl
@[simp] theorem nL_orders : (nL l).orders = l.orders.map nO := rfl
@[simp] theorem conflict_n (r : Order) : selfTradeConflict (nI o) (nO r) = selfTradeConflict o r := rfl
@[simp] theorem canMatch_n (p : Nat) : canMatchPrice (nI o) p = canMatchPrice o p := rfl
end Fields

/-- The fuel-limited matching loop commutes with the normal form. -/
theorem doMatch_norm : ∀ (f : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp),
    nR (doMatch f inc bids asks trades tm) = nR (doMatch f (nI inc) (bids.map nL) (asks.map nL) trades 0) := by
  intro f
  induction f with
  | zero => intro inc bids asks trades tm; simp [doMatch, nR]
  | succ f ih =>
    intro inc bids asks trades tm
    rw [doMatch.eq_2, doMatch.eq_2]
    by_cases hd : (inc.remainingQty == 0 || inc.status == OrderStatus.cancelled) = true
    · rw [if_pos hd, if_pos (show ((nI inc).remainingQty == 0 || (nI inc).status == OrderStatus.cancelled) = true from hd)]
      simp [nR]
    · rw [if_neg hd, if_neg (show ¬ ((nI inc).remainingQty == 0 || (nI inc).status == OrderStatus.cancelled) = true from hd)]
      rw [nI_side]
      cases hs : inc.side
      · cases asks with
        | nil => dsimp only; simp [nR]
        | cons level rest =>
          dsimp only
          rw [List.map_cons]
          dsimp only
          rw [nL_price, canMatch_n]
          by_cases hp : (!canMatchPrice inc level.price) = true
          · rw [if_pos hp, if_pos hp]; simp [nR, nI]
          · rw [if_neg hp, if_neg hp, nL_orders]
            cases ho : level.orders with
            | nil =>
              dsimp only
              refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
              simp
            | cons resting ro =>
              dsimp only
              rw [List.map_cons]
              dsimp only
              rw [nO_vis, conflict_n]
              by_cases hz : (resting.visibleQty == 0 && !selfTradeConflict inc resting) = true
              · rw [if_pos hz, if_pos hz]
                refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                cases ro <;> simp [List.map_map]
              · rw [if_neg hz, if_neg hz]
                by_cases hc : selfTradeConflict inc resting = true
                · rw [if_pos hc, if_pos hc, nI_policy]
                  cases hpol : inc.stpPolicy.getD STPPolicy.cancelNewest
                  · simp [nR, nI]
                  · dsimp only; (refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm); cases ro <;> simp [List.map_map, nI])
                  · cases ro <;> simp [nR, nI, List.map_map]
                  · dsimp only
                    rw [nI_rem, nO_rem, nO_disp]
                    by_cases hq : (min inc.remainingQty resting.visibleQty == 0) = true
                    · rw [if_pos hq, if_pos hq]; (refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm); cases ro <;> simp [List.map_map, nI])
                    · rw [if_neg hq, if_neg hq]
                      by_cases hr : (resting.remainingQty - min inc.remainingQty resting.visibleQty == 0) = true
                      · rw [if_pos hr, if_pos hr]; (refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm); cases ro <;> simp [List.map_map, nI])
                      · rw [if_neg hr, if_neg hr]
                        by_cases hv : (resting.visibleQty - min inc.remainingQty resting.visibleQty == 0 && resting.displayQty.isSome) = true
                        · rw [if_pos hv, if_pos hv]
                          refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                          simp [List.map_map, nI, nO, nL]
                        · rw [if_neg hv, if_neg hv]
                          refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                          simp [List.map_map, nI, nO, nL]
                · rw [if_neg hc, if_neg hc]
                  rw [nI_rem, nO_rem, nO_disp]
                  by_cases hr : (resting.remainingQty - min inc.remainingQty resting.visibleQty == 0) = true
                  · rw [if_pos hr, if_pos hr]
                    refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                    cases ro <;> simp [List.map_map, nI, nO, nL]
                  · rw [if_neg hr, if_neg hr]
                    by_cases hv : (resting.visibleQty - min inc.remainingQty resting.visibleQty == 0 && resting.displayQty.isSome) = true
                    · rw [if_pos hv, if_pos hv]
                      refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                      simp [List.map_map, nI, nO, nL]
                    · rw [if_neg hv, if_neg hv]
                      refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                      simp [List.map_map, nI, nO, nL]
      · cases bids with
        | nil => dsimp only; simp [nR]
        | cons level rest =>
          dsimp only
          rw [List.map_cons]
          dsimp only
          rw [nL_price, canMatch_n]
          by_cases hp : (!canMatchPrice inc level.price) = true
          · rw [if_pos hp, if_pos hp]; simp [nR, nI]
          · rw [if_neg hp, if_neg hp, nL_orders]
            cases ho : level.orders with
            | nil =>
              dsimp only
              refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
              simp
            | cons resting ro =>
              dsimp only
              rw [List.map_cons]
              dsimp only
              rw [nO_vis, conflict_n]
              by_cases hz : (resting.visibleQty == 0 && !selfTradeConflict inc resting) = true
              · rw [if_pos hz, if_pos hz]
                refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                cases ro <;> simp [List.map_map]
              · rw [if_neg hz, if_neg hz]
                by_cases hc : selfTradeConflict inc resting = true
                · rw [if_pos hc, if_pos hc, nI_policy]
                  cases hpol : inc.stpPolicy.getD STPPolicy.cancelNewest
                  · simp [nR, nI]
                  · dsimp only; (refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm); cases ro <;> simp [List.map_map, nI])
                  · cases ro <;> simp [nR, nI, List.map_map]
                  · dsimp only
                    rw [nI_rem, nO_rem, nO_disp]
                    by_cases hq : (min inc.remainingQty resting.visibleQty == 0) = true
                    · rw [if_pos hq, if_pos hq]; (refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm); cases ro <;> simp [List.map_map, nI])
                    · rw [if_neg hq, if_neg hq]
                      by_cases hr : (resting.remainingQty - min inc.remainingQty resting.visibleQty == 0) = true
                      · rw [if_pos hr, if_pos hr]; (refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm); cases ro <;> simp [List.map_map, nI])
                      · rw [if_neg hr, if_neg hr]
                        by_cases hv : (resting.visibleQty - min inc.remainingQty resting.visibleQty == 0 && resting.displayQty.isSome) = true
                        · rw [if_pos hv, if_pos hv]
                          refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                          simp [List.map_map, nI, nO, nL]
                        · rw [if_neg hv, if_neg hv]
                          refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                          simp [List.map_map, nI, nO, nL]
                · rw [if_neg hc, if_neg hc]
                  rw [nI_rem, nO_rem, nO_disp]
                  by_cases hr : (resting.remainingQty - min inc.remainingQty resting.visibleQty == 0) = true
                  · rw [if_pos hr, if_pos hr]
                    refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                    cases ro <;> simp [List.map_map, nI, nO, nL]
                  · rw [if_neg hr, if_neg hr]
                    by_cases hv : (resting.visibleQty - min inc.remainingQty resting.visibleQty == 0 && resting.displayQty.isSome) = true
                    · rw [if_pos hv, if_pos hv]
                      refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                      simp [List.map_map, nI, nO, nL]
                    · rw [if_neg hv, if_neg hv]
                      refine (ih _ _ _ _ _).trans (Eq.trans ?_ (ih _ _ _ _ _).symm)
                      simp [List.map_map, nI, nO, nL]


theorem doMatch_congr {f : Nat} {inc1 inc2 : Order} {bids1 bids2 asks1 asks2 : List PriceLevel}
    {trades : List Trade} {tm1 tm2 : Timestamp} (hi : nI inc1 = nI inc2)
    (hb : bids1.map nL = bids2.map nL) (ha : asks1.map nL = asks2.map nL) :
    nR (doMatch f inc1 bids1 asks1 trades tm1) = nR (doMatch f inc2 bids2 asks2 trades tm2) := by
  rw [doMatch_norm, doMatch_norm f inc2, hi, hb, ha]

-- ============================================================================
-- The view of a book as a normal form
-- ============================================================================

/-- A book without the fields `bookView` drops. -/
def nB (b : BookState) : BookState :=
  { bids := b.bids.map nL, asks := b.asks.map nL, stops := b.stops.map nO, lastTradePrice := none,
    nextId := 0, clock := 0 }

def ofOV (v : OrderView) : Order :=
  { id := v.id, side := v.side, orderType := v.orderType, tif := v.tif, price := v.price,
    stopPrice := v.stopPrice, qty := v.qty, remainingQty := v.remainingQty, minQty := v.minQty,
    displayQty := v.displayQty, visibleQty := v.visibleQty, postOnly := false, status := .new_,
    timestamp := 0, stpGroup := v.stpGroup, stpPolicy := v.stpPolicy }

def ofLV (v : LevelView) : PriceLevel := { price := v.price, orders := v.orders.map ofOV }

theorem nO_eq (o : Order) : nO o = ofOV (orderView o) := rfl
theorem nL_eq (l : PriceLevel) : nL l = ofLV (levelView l) := by
  simp [nL, ofLV, levelView, List.map_map, Function.comp_def, nO_eq]
theorem levelView_nL (l : PriceLevel) : levelView (nL l) = levelView l := by
  simp [nL, levelView, List.map_map, Function.comp_def, orderView, nO]

theorem views_iff (L1 L2 : List PriceLevel) :
    L1.map levelView = L2.map levelView ↔ L1.map nL = L2.map nL := by
  constructor
  · intro h
    have : (L1.map levelView).map ofLV = (L2.map levelView).map ofLV := by rw [h]
    simpa [List.map_map, Function.comp_def, ← nL_eq] using this
  · intro h
    have : (L1.map nL).map levelView = (L2.map nL).map levelView := by rw [h]
    simpa [List.map_map, Function.comp_def, levelView_nL] using this

theorem oviews_iff (L1 L2 : List Order) :
    L1.map orderView = L2.map orderView ↔ L1.map nO = L2.map nO := by
  constructor
  · intro h
    have : (L1.map orderView).map ofOV = (L2.map orderView).map ofOV := by rw [h]
    simpa [List.map_map, Function.comp_def, ← nO_eq] using this
  · intro h
    have : (L1.map nO).map orderView = (L2.map nO).map orderView := by rw [h]
    simpa [List.map_map, Function.comp_def, orderView, nO] using this

theorem bookView_iff (b1 b2 : BookState) : bookView b1 = bookView b2 ↔ nB b1 = nB b2 := by
  simp only [bookView, nB, BookView.mk.injEq, BookState.mk.injEq, views_iff, oviews_iff, and_true]

-- ============================================================================
-- Spec functions that read only the view
-- ============================================================================

theorem allBookOrders_nB (b : BookState) : allBookOrders (nB b) = (allBookOrders b).map nO := by
  simp [allBookOrders, nB, List.flatMap_map, List.map_flatMap, nL]

theorem idOnBook_nB (b : BookState) (n : Nat) : idOnBook (nB b) n = idOnBook b n := by
  simp [idOnBook, allBookOrders_nB, List.any_map, Function.comp_def]

theorem bookSize_nB (b : BookState) : bookSize (nB b) = bookSize b := by
  unfold bookSize; rw [allBookOrders_nB]; simp [nB]

theorem wouldCross_nB (o : Order) (b : BookState) : wouldCross o (nB b) = wouldCross o b := by
  unfold wouldCross bestAskPrice bestBidPrice
  cases o.price <;> cases o.side <;> simp [nB] <;> cases b.bids <;> cases b.asks <;> simp

theorem postOnlyCode_nB (o : Order) (b : BookState) : postOnlyCode o (nB b) = postOnlyCode o b := by
  simp [postOnlyCode, wouldCross_nB]

theorem computeMatchFuel_nB (b : BookState) (s : Side) :
    computeMatchFuel (nB b) s = computeMatchFuel b s := by
  unfold computeMatchFuel contraLevels
  cases s <;> simp [nB, List.foldl_map, nL]

theorem insertDesc_nL (o : Order) (p : Nat) : ∀ (L : List PriceLevel),
    (insertDesc L o p).map nL = insertDesc (L.map nL) (nO o) p
  | [] => rfl
  | l :: rest => by
    simp only [insertDesc, List.map_cons, nL_price]
    split
    · simp
    · split
      · simp [nL]
      · simp only [List.map_cons, insertDesc_nL o p rest]

theorem insertAsc_nL (o : Order) (p : Nat) : ∀ (L : List PriceLevel),
    (insertAsc L o p).map nL = insertAsc (L.map nL) (nO o) p
  | [] => rfl
  | l :: rest => by
    simp only [insertAsc, List.map_cons, nL_price]
    split
    · simp
    · split
      · simp [nL]
      · simp only [List.map_cons, insertAsc_nL o p rest]

theorem nB_idem (b : BookState) : nB (nB b) = nB b := by
  simp [nB, List.map_map, Function.comp_def]

theorem insertOrder_nB (A : BookState) (inc : Order) (hasT : Bool) :
    nB (insertOrder A inc hasT) = nB (insertOrder (nB A) (nI inc) hasT) := by
  unfold insertOrder
  cases hs : inc.side <;> simp [nB, hs, insertDesc_nL, insertAsc_nL, List.map_map, Function.comp_def] <;>
    rfl

theorem dispose_nB (inc : Order) (A : BookState) (t : List Trade) :
    nB (dispose inc A t) = nB (dispose (nI inc) (nB A) t) := by
  unfold dispose
  have e1 : (nI inc).tif = inc.tif := rfl
  have e2 : (nI inc).orderType = inc.orderType := rfl
  rw [nI_rem, nI_status, e1, e2]
  by_cases h1 : (inc.remainingQty == 0 || inc.status == .cancelled) = true
  · rw [if_pos h1, if_pos h1]; exact (nB_idem A).symm
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (inc.tif == .ioc) = true
    · rw [if_pos h2, if_pos h2]; exact (nB_idem A).symm
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : (inc.orderType == .market) = true
      · rw [if_pos h3, if_pos h3]; exact (nB_idem A).symm
      · rw [if_neg h3, if_neg h3]; exact insertOrder_nB A inc _

theorem removeLevelOrder_nL (n : Nat) (L : List PriceLevel) :
    (removeLevelOrder L n).map nL = removeLevelOrder (L.map nL) n := by
  rw [removeLevelOrder_eq, removeLevelOrder_eq, List.map_filterMap, List.filterMap_map]
  congr 1
  funext l
  have hf : (l.orders.map nO).filter (·.id != n) = (l.orders.filter (·.id != n)).map nO := by
    rw [List.filter_map]; rfl
  simp only [Function.comp, dropStep, nL_orders, hf, List.isEmpty_map]
  split <;> simp [nL]

/-- The search `findOrderOnBook` makes on one side. -/
def srch (n : Nat) (sd : Side) (level : PriceLevel) : Option (Side × Order) :=
  level.orders.findSome? fun order => if order.id == n then some (sd, order) else none

def nP (p : Side × Order) : Side × Order := (p.1, nO p.2)

theorem srch_side (n : Nat) (sd : Side) (L : List PriceLevel) :
    (L.map nL).findSome? (srch n sd) = (L.findSome? (srch n sd)).map nP := by
  rw [List.findSome?_map, List.map_findSome?]
  congr 1
  funext level
  simp only [Function.comp, srch, nL_orders]
  rw [List.findSome?_map, List.map_findSome?]
  congr 1
  funext o
  simp only [Function.comp, nO_id]
  split <;> rfl

theorem findOrderOnBook_nB (b : BookState) (n : Nat) :
    findOrderOnBook (nB b) n = (findOrderOnBook b n).map nP := by
  have hb := srch_side n .buy b.bids
  have ha := srch_side n .sell b.asks
  unfold findOrderOnBook
  simp only [nB]
  unfold srch at hb ha
  rw [hb, ha]
  cases (b.bids.findSome? fun level => level.orders.findSome? fun order =>
    if order.id == n then some (Side.buy, order) else none) <;> rfl

theorem cancelOrder_nB (b : BookState) (n : Nat) :
    (cancelOrder (nB b) n).map nB = (cancelOrder b n).map nB := by
  unfold cancelOrder
  rw [findOrderOnBook_nB]
  cases findOrderOnBook b n with
  | none => rfl
  | some p =>
    obtain ⟨sd, o⟩ := p
    cases sd <;> simp [nP, nB, ← removeLevelOrder_nL, List.map_map, Function.comp_def]

-- ============================================================================
-- processB depends only on the view (on a book without stops)
-- ============================================================================

theorem mrOf_congr {b1 b2 : BookState} (hn : nB b1 = nB b2) (o : Order) :
    nR (mrOf b1 o) = nR (mrOf b2 o) := by
  unfold mrOf
  have hf : computeMatchFuel b1 o.side = computeMatchFuel b2 o.side := by
    rw [← computeMatchFuel_nB b1, hn, computeMatchFuel_nB]
  rw [hf]
  apply doMatch_congr
  · simp [nI, o1Of]
  · exact congrArg BookState.bids hn
  · exact congrArg BookState.asks hn

theorem nB_afterMatch {b1 b2 : BookState} (hn : nB b1 = nB b2) (o : Order) :
    nB (afterMatch b1 o) = nB (afterMatch b2 o) := by
  have hm := mrOf_congr hn o
  have hs : b1.stops.map nO = b2.stops.map nO := congrArg BookState.stops hn
  simp only [nB, afterMatch, BookState.mk.injEq]
  refine ⟨congrArg MatchResult.bids hm, congrArg MatchResult.asks hm, hs, trivial, trivial, trivial⟩

/-- What `processWithId` does with an order `processB` accepted, through the view. -/
theorem pwi_cases {r : CRequest} {o : Order} {b : BookState} (hts : r.toSpec = some o)
    (hs : b.stops = []) :
    (postOnlyCode o b = .rejectedPostOnly →
      (processWithId b o).trades = [] ∧ nB (processWithId b o).book = nB b) ∧
    (postOnlyCode o b = .accepted →
      (processWithId b o).trades = (mrOf b o).trades ∧
      nB (processWithId b o).book = nB (dispose (mrOf b o).incoming (afterMatch b o) (mrOf b o).trades)) := by
  have hsd := specOrd_of hts
  have hns := toSpec_not_stop hts
  have hwf := toSpec_wellFormed hts
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨ht, hb, ha, hst⟩ := postOnly_reject_agrees hns hc
    refine ⟨ht, ?_⟩
    simp only [nB, hb, ha, hst]
  · by_cases hpo : o.postOnly = true
    · have h3 : r.orderType = 3 := by
        have := hsd.po; rw [hpo] at this; exact of_decide_eq_true this.symm
      have hwc : wouldCross o b = false := by
        cases h : wouldCross o b
        · rfl
        · simp [postOnlyCode, hpo, h] at hc
      have hn1 : r.orderType ≠ 1 := by rw [h3]; decide
      have hn12 : ¬(r.orderType = 1 ∨ r.orderType = 2) := by rw [h3]; decide
      obtain ⟨ht, hv⟩ := processWithId_postOnly hs hns hpo (by rw [wouldCross_o1]; exact hwc)
        (by rw [hsd.rem, ← hsd.qty]; exact Nat.pos_iff_ne_zero.mp hwf.1)
        hsd.st (by rw [hsd.tif, if_neg hn12]) (by rw [hsd.ty, if_neg hn1])
        ⟨_, by rw [hsd.price, if_neg hn1]⟩
      exact ⟨ht, (bookView_iff _ _).mp hv⟩
    · have hfok : o.tif ≠ .fok := by rw [hsd.tif]; split <;> decide
      have hmtl : o.orderType ≠ .marketToLimit := by rw [hsd.ty]; split <;> decide
      obtain ⟨ht, hv⟩ := processWithId_match hs hns hfok hsd.minq hmtl (by simpa using hpo)
      exact ⟨ht, (bookView_iff _ _).mp hv⟩

theorem postOnlyCode_cases (o : Order) (b : BookState) :
    postOnlyCode o b = .rejectedPostOnly ∨ postOnlyCode o b = .accepted := by
  unfold postOnlyCode; split <;> simp

/-- **`processB` reads only the view** of a book without stops: the result code,
    the trades and the view of the new book agree. -/
theorem processB_congr (cap : Nat) {b1 b2 : BookState} (hs1 : b1.stops = []) (hs2 : b2.stops = [])
    (hn : nB b1 = nB b2) (req : Req) :
    (processB cap b1 req).1 = (processB cap b2 req).1 ∧
    (processB cap b1 req).2.trades = (processB cap b2 req).2.trades ∧
    nB (processB cap b1 req).2.book = nB (processB cap b2 req).2.book := by
  cases req with
  | order r =>
    unfold processB
    simp only
    cases hot : decodeOrderType r.orderType with
    | none => exact ⟨rfl, rfl, hn⟩
    | some ot =>
      simp only
      cases hts : r.toSpec with
      | none => exact ⟨rfl, rfl, hn⟩
      | some o =>
        simp only
        have hid : idOnBook b1 o.id = idOnBook b2 o.id := by
          rw [← idOnBook_nB b1, hn, idOnBook_nB]
        have hsz : bookSize b1 = bookSize b2 := by rw [← bookSize_nB b1, hn, bookSize_nB]
        have hpc : postOnlyCode o b1 = postOnlyCode o b2 := by
          rw [← postOnlyCode_nB o b1, hn, postOnlyCode_nB]
        rw [hid, hsz]
        by_cases h1 : qmax cap < r.qty.toNat
        · rw [if_pos h1, if_pos h1]; exact ⟨rfl, rfl, hn⟩
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : idOnBook b2 o.id = true
          · rw [if_pos h2, if_pos h2]; exact ⟨rfl, rfl, hn⟩
          · rw [if_neg h2, if_neg h2]
            by_cases h3 : (requestMayRest r && decide (cap ≤ bookSize b2)) = true
            · rw [if_pos h3, if_pos h3]; exact ⟨rfl, rfl, hn⟩
            · rw [if_neg h3, if_neg h3]
              refine ⟨hpc, ?_⟩
              have p1 := pwi_cases hts hs1
              have p2 := pwi_cases hts hs2
              rcases postOnlyCode_cases o b1 with hc | hc
              · have hc2 : postOnlyCode o b2 = .rejectedPostOnly := hpc ▸ hc
                obtain ⟨t1, v1⟩ := p1.1 hc
                obtain ⟨t2, v2⟩ := p2.1 hc2
                exact ⟨by rw [t1, t2], by rw [v1, v2, hn]⟩
              · have hc2 : postOnlyCode o b2 = .accepted := hpc ▸ hc
                obtain ⟨t1, v1⟩ := p1.2 hc
                obtain ⟨t2, v2⟩ := p2.2 hc2
                have hm := mrOf_congr hn o
                have htr : (mrOf b1 o).trades = (mrOf b2 o).trades := by
                  have := congrArg MatchResult.trades hm; simpa [nR] using this
                have hinc : nI (mrOf b1 o).incoming = nI (mrOf b2 o).incoming := by
                  have := congrArg MatchResult.incoming hm; simpa [nR] using this
                refine ⟨by rw [t1, t2, htr], ?_⟩
                rw [v1, v2, dispose_nB, dispose_nB (mrOf b2 o).incoming, hinc, nB_afterMatch hn o, htr]
  | cancel id =>
    have hc := cancelOrder_nB b1 id.toNat
    have hc2 := cancelOrder_nB b2 id.toNat
    rw [hn] at hc
    have key : (cancelOrder b1 id.toNat).map nB = (cancelOrder b2 id.toNat).map nB := hc.symm.trans hc2
    unfold processB
    simp only
    cases e1 : cancelOrder b1 id.toNat with
    | none =>
      cases e2 : cancelOrder b2 id.toNat with
      | none => exact ⟨rfl, rfl, hn⟩
      | some x => rw [e1, e2] at key; simp at key
    | some x =>
      cases e2 : cancelOrder b2 id.toNat with
      | none => rw [e1, e2] at key; simp at key
      | some y =>
        rw [e1, e2] at key
        simp only [Option.map_some, Option.some.injEq] at key
        exact ⟨rfl, rfl, key⟩

-- ============================================================================
-- Runs
-- ============================================================================

/-- One step's observation as the C API reports it: the result code, the
    trades, and the book restricted to what C stores. -/
abbrev StepObs := UInt8 × List TradeObs × BookView

/-- The spec's observations along `runB`. -/
def specTrace (cap : Nat) : BookState → List Req → List StepObs
  | _, [] => []
  | b, q :: qs =>
    (codeOf (processB cap b q).1, (processB cap b q).2.trades.map tradeObs,
      bookView (processB cap b q).2.book) :: specTrace cap (processB cap b q).2.book qs

/-- `specTrace` follows `runB`: its last book is `runB`'s. -/
theorem specTrace_runB (cap : Nat) : ∀ (b : BookState) (q : Req) (qs : List Req),
    (specTrace cap b (qs ++ [q])).getLast? =
      some (codeOf (processB cap (runB cap b qs) q).1,
        (processB cap (runB cap b qs) q).2.trades.map tradeObs,
        bookView (runB cap b (qs ++ [q])))
  | b, q, [] => by simp [specTrace, runB]
  | b, q, q' :: qs => by
    have ih := specTrace_runB cap (processB cap b q').2.book q qs
    simp only [List.cons_append, specTrace, runB] at ih ⊢
    rw [List.getLast?_cons, ih]; rfl

variable {S : Type} [EngineDb S]

open EngineDb

/-- The matcher run: each request through its entry function, with one fuel. -/
def matcherRun (fuel : Nat) : S → List Req → Except Err (List (StepObs × S))
  | _, [] => .ok []
  | s, q :: qs =>
    match runEntry program fuel (entryOf q) (argsOf q) s with
    | .ok (.code k, s', ts) =>
      match matcherRun fuel s' qs with
      | .ok rest => .ok (((k, ts, bookView (absBook (view s'))), s') :: rest)
      | .error e => .error e
    | .ok _ => .error .type
    | .error e => .error e

theorem runEntry_mono {P : Program} {f f' : Nat} {fname : Ident} {args : List Val} {s : S} {r}
    (h : runEntry P f fname args s = .ok r) (hle : f ≤ f') : runEntry P f' fname args s = .ok r := by
  unfold runEntry at h ⊢
  cases hf : lookupFun P fname with
  | error e => rw [hf] at h; cases h
  | ok fd =>
    rw [hf] at h
    simp only [bind, Except.bind] at h ⊢
    cases hp : bindParams fd.params args with
    | error e => rw [hp] at h; cases h
    | ok penv =>
      rw [hp] at h
      simp only at h ⊢
      cases he : execStmt P f fd.body { store := s, env := penv ++ fd.locals.map fun (x, t) => (x, t.default), trades := [] } with
      | error e => rw [he] at h; cases h
      | ok x =>
        rw [he] at h
        rw [execStmt_mono P he hle]
        exact h

theorem matcherRun_mono {f f' : Nat} (hle : f ≤ f') : ∀ (s : S) (qs : List Req) outs,
    matcherRun f s qs = .ok outs → matcherRun f' s qs = .ok outs
  | _, [], _, h => h
  | s, q :: qs, outs, h => by
    unfold matcherRun at h ⊢
    cases hr : runEntry program f (entryOf q) (argsOf q) s with
    | error e => rw [hr] at h; cases h
    | ok x =>
      rw [hr] at h
      rw [runEntry_mono hr hle]
      obtain ⟨v, s', ts⟩ := x
      cases v with
      | code k =>
        simp only at h ⊢
        cases hm : matcherRun f s' qs with
        | error e => rw [hm] at h; cases h
        | ok rest =>
          rw [hm] at h
          rw [matcherRun_mono hle s' qs rest hm]
          exact h
      | _ => cases h

theorem stops_nil_of_nB {b b' : BookState} (h : nB b = nB b') (hs : b.stops = []) : b'.stops = [] := by
  have := congrArg BookState.stops h
  simp only [nB, hs, List.map_nil] at this
  exact List.map_eq_nil_iff.mp this.symm

theorem run_from (hcap : CapOk S) : ∀ (qs : List Req) (s : S) (b : BookState), Inv s → b.stops = [] →
    nB (absBook (view s)) = nB b →
    ∃ fuel outs, matcherRun fuel s qs = .ok outs ∧
      outs.map Prod.fst = specTrace (capacity (S := S)) b qs ∧ ∀ x ∈ outs, Inv x.2
  | [], s, b, _, _, _ => ⟨0, [], rfl, rfl, fun _ h => by cases h⟩
  | q :: qs, s, b, hI, hs, hn => by
    obtain ⟨f, s', ts, hrun, htr, hbv, hI'⟩ := matcher_refines hcap hI q
    have hc := processB_congr (capacity (S := S)) (b1 := absBook (view s)) (b2 := b) rfl hs hn q
    obtain ⟨hcode, htrades, hbook⟩ := hc
    have hn' : nB (absBook (view s')) = nB (processB (capacity (S := S)) b q).2.book := by
      rw [(bookView_iff _ _).mp hbv]; exact hbook
    have hs' : (processB (capacity (S := S)) b q).2.book.stops = [] := stops_nil_of_nB hn' rfl
    obtain ⟨f2, outs, hrun2, hobs, hinv⟩ := run_from hcap qs s' _ hI' hs' hn'
    refine ⟨max f f2, ((codeOf (specStep s q).1, ts, bookView (absBook (view s'))), s') :: outs, ?_, ?_, ?_⟩
    · unfold matcherRun
      rw [runEntry_mono hrun (Nat.le_max_left f f2)]
      simp only
      rw [matcherRun_mono (Nat.le_max_right f f2) s' qs outs hrun2]
    · simp only [List.map_cons, specTrace, hobs]
      congr 1
      have hc' : (specStep s q).1 = (processB (capacity (S := S)) b q).1 := hcode
      simp only [specStep] at htrades hbv htr
      rw [htr, htrades, hc', (bookView_iff _ _).mpr hn']
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hI'
      · exact hinv x hx

/-- **The run-level theorem.** For every request list, the matcher run from the
    initial store returns `.ok`, its observations (result code, trades, book
    view after each step) equal those of `runB` from the empty book, and `Inv`
    holds after every step. -/
theorem matcher_run_refines (hcap : CapOk S) (qs : List Req) :
    ∃ fuel outs, matcherRun fuel (EngineDb.init : S) qs = .ok outs ∧
      outs.map Prod.fst = specTrace (capacity (S := S)) BookState.empty qs ∧ ∀ x ∈ outs, Inv x.2 :=
  run_from hcap qs _ _ inv_init rfl (by rw [EngineDb.init_view]; rfl)

end MatcherRun
