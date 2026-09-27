import Bridge.ProcessB

/-!
# Phase 4: the spec side of the matching loop

The matching loop of the generated matcher is related to the spec's
`doMatch` through its remaining computation (LOOP-INVARIANT.md). This file
gives the spec facts that relation needs:

* `doMatch_fuel_stable`: any fuel above `matchMeasure` of the contra side
  gives the same result. So the remaining computation from a state `σ` can be
  stated at the spec's own fuel for `σ`, `rest σ := dm (matchMeasure σ + 1) σ`,
  whatever the iteration count so far.
* `dm`: `doMatch` with the book given as the incoming order's own side and
  contra side, so that one lemma covers both sides.
* One unfolding lemma per `doMatch` branch the matcher can reach, each of the
  form `dm (n + 1) σ = dm n σ'`, and `rest_step`: such a step with a smaller
  measure leaves `rest` unchanged.
-/

namespace MatcherSpec

open EngineDbApi EngineDbAbs ProcessB

-- ============================================================================
-- Fuel stability
-- ============================================================================

/-- The contra side of `doMatch`'s arguments. -/
def cOf (inc : Order) (bids asks : List PriceLevel) : List PriceLevel :=
  match inc.side with | .buy => asks | .sell => bids

theorem mm_drop' {level : PriceLevel} {rl : List PriceLevel} {r : Order} {ro : List Order} {n : Nat}
    (hq : level.orders = r :: ro)
    (hm : totalRemaining (level :: rl) + orderCount (level :: rl) + (level :: rl).length < n + 1) :
    totalRemaining (if ro = [] then rl else { price := level.price, orders := ro } :: rl) +
      orderCount (if ro = [] then rl else { price := level.price, orders := ro } :: rl) +
      (if ro = [] then rl else { price := level.price, orders := ro } :: rl).length < n := by
  have := matchMeasure_drop_head_order level rl r r ro hq
  have e : (if ro.isEmpty then rl else { level with orders := ro } :: rl) =
      (if ro = [] then rl else { price := level.price, orders := ro } :: rl) := by
    cases ro <;> rfl
  rw [e] at this; unfold matchMeasure at this; omega

theorem mm_skip' {level : PriceLevel} {rl : List PriceLevel} {n : Nat}
    (hq : level.orders = [])
    (hm : totalRemaining (level :: rl) + orderCount (level :: rl) + (level :: rl).length < n + 1) :
    totalRemaining rl + orderCount rl + rl.length < n := by
  have := matchMeasure_skip_empty_level level rl default hq
  unfold matchMeasure at this; omega

theorem mm_mod' {level : PriceLevel} {rl : List PriceLevel} {newQ : List Order} {n : Nat}
    (hlen : newQ.length = level.orders.length) (hdec : orderSum newQ < orderSum level.orders)
    (hm : totalRemaining (level :: rl) + orderCount (level :: rl) + (level :: rl).length < n + 1) :
    totalRemaining ({ price := level.price, orders := newQ } :: rl) +
      orderCount ({ price := level.price, orders := newQ } :: rl) +
      ({ price := level.price, orders := newQ } :: rl).length < n := by
  have := matchMeasure_modify_head_level_orders level rl default newQ hlen hdec
  unfold matchMeasure at this; omega

theorem dec_aux1 (R I V O : Nat) (h1 : ¬ I = 0) (h2 : ¬ V = 0) (h3 : ¬ R - min I V = 0) :
    R - min I V + O < R + O := by omega

theorem dec_aux2 (R I V O : Nat) (h1 : ¬ I = 0) (h2 : ¬ V = 0) (h3 : ¬ R - min I V = 0) :
    O + (R - min I V + 0) < R + O := by omega

/-- **Fuel stability of `doMatch`.** Above `matchMeasure` of the contra side,
    more fuel does not change the result. -/
theorem doMatch_fuel_stable (f : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) :
    f > matchMeasure (cOf inc bids asks) inc → ∀ g, f ≤ g →
    doMatch g inc bids asks trades tm = doMatch f inc bids asks trades tm := by
  fun_induction doMatch f inc bids asks trades tm
  all_goals intro hm g hg
  · omega
  all_goals obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  all_goals first
    | (rw [doMatch.eq_2]; simp_all (config := {zetaDelta := true}); done)
    | (rename_i ih
       refine Eq.trans ?_ (ih ?_ g' (by omega))
       · rw [doMatch.eq_2]; simp_all (config := {zetaDelta := true})
       · expose_names
         cases hs : inc.side <;> simp_all (config := {zetaDelta := true}) [cOf]
         all_goals first
           | obtain ⟨rfl, rfl⟩ := h_4 | obtain ⟨rfl, rfl⟩ := h_5 | obtain ⟨rfl, rfl⟩ := h_6
           | obtain ⟨rfl, rfl⟩ := h_7 | obtain ⟨rfl, rfl⟩ := h_8 | obtain ⟨rfl, rfl⟩ := h_9
           | obtain ⟨rfl, rfl⟩ := h_10 | obtain ⟨rfl, rfl⟩ := h_11 | obtain ⟨rfl, rfl⟩ := h_12
         all_goals simp only [matchMeasure] at hm ⊢
         all_goals first
           | exact mm_drop' h_3 hm
           | exact mm_skip' h_3 hm
           | (refine mm_mod' ?_ ?_ hm
              · rw [h_3]; simp
              · rw [h_3]
                simp only [orderSum_append, orderSum]
                have hr0 := h.1
                first
                  | exact dec_aux1 _ _ _ _ (by assumption) (by assumption) (by assumption)
                  | exact dec_aux2 _ _ _ _ (by assumption) (by assumption) (by assumption)))

-- ============================================================================
-- doMatch by own side and contra side
-- ============================================================================

def bidsOf : Side → List PriceLevel → List PriceLevel → List PriceLevel
  | .buy, own, _ => own
  | .sell, _, contra => contra

def asksOf : Side → List PriceLevel → List PriceLevel → List PriceLevel
  | .buy, _, contra => contra
  | .sell, own, _ => own

/-- `doMatch` with the book as the incoming order's own and contra sides. -/
def dm (f : Nat) (inc : Order) (own contra : List PriceLevel) (trades : List Trade)
    (tm : Timestamp) : MatchResult :=
  doMatch f inc (bidsOf inc.side own contra) (asksOf inc.side own contra) trades tm

/-- The result of a terminal state. -/
def term (inc : Order) (own contra : List PriceLevel) (trades : List Trade) (tm : Timestamp) :
    MatchResult :=
  { incoming := inc, bids := bidsOf inc.side own contra, asks := asksOf inc.side own contra,
    trades := trades, clock := tm }

theorem cOf_of (inc : Order) (own contra : List PriceLevel) :
    cOf inc (bidsOf inc.side own contra) (asksOf inc.side own contra) = contra := by
  unfold cOf bidsOf asksOf; cases inc.side <;> rfl

theorem dm_stable {f g : Nat} {inc : Order} {own contra : List PriceLevel} {trades : List Trade}
    {tm : Timestamp} (hf : f > matchMeasure contra inc) (hg : f ≤ g) :
    dm g inc own contra trades tm = dm f inc own contra trades tm := by
  unfold dm
  exact doMatch_fuel_stable f inc _ _ trades tm (by rw [cOf_of]; exact hf) g hg

/-- The spec's remaining computation from a state, at the spec's own fuel. -/
def rest (inc : Order) (own contra : List PriceLevel) (trades : List Trade) (tm : Timestamp) :
    MatchResult :=
  dm (matchMeasure contra inc + 1) inc own contra trades tm

/-- **One spec step keeps the remaining computation.** -/
theorem rest_step {inc inc' : Order} {own contra contra' : List PriceLevel}
    {trades trades' : List Trade} {tm : Timestamp}
    (h : ∀ n, dm (n + 1) inc own contra trades tm = dm n inc' own contra' trades' tm)
    (hlt : matchMeasure contra' inc' < matchMeasure contra inc) :
    rest inc own contra trades tm = rest inc' own contra' trades' tm := by
  unfold rest
  rw [h]
  exact dm_stable (f := matchMeasure contra' inc' + 1) (Nat.lt_succ_self _) (by omega)

/-- A spec step into a terminal state keeps the remaining computation. -/
theorem rest_step_done {inc inc' : Order} {own contra contra' : List PriceLevel}
    {trades trades' : List Trade} {tm : Timestamp}
    (h : ∀ n, dm (n + 1) inc own contra trades tm = dm n inc' own contra' trades' tm)
    (hd : (inc'.remainingQty == 0 || inc'.status == .cancelled) = true) :
    rest inc own contra trades tm = rest inc' own contra' trades' tm := by
  unfold rest
  rw [h]
  unfold dm
  cases matchMeasure contra inc <;> cases matchMeasure contra' inc' <;>
    simp only [doMatch, hd, if_true]

/-- The whole spec run is the remaining computation from the start. -/
theorem rest_start {f : Nat} {inc : Order} {own contra : List PriceLevel} {trades : List Trade}
    {tm : Timestamp} (hf : f > matchMeasure contra inc) :
    dm f inc own contra trades tm = rest inc own contra trades tm := by
  unfold rest; exact dm_stable (Nat.lt_succ_self _) hf

-- ============================================================================
-- Terminal states
-- ============================================================================

theorem done_of_cancelled {o : Order} (h : o.status = .cancelled) :
    (o.remainingQty == 0 || o.status == .cancelled) = true := by
  rw [h]; simp only [Bool.or_eq_true]; exact Or.inr (by decide)

theorem dm_done {n : Nat} {inc : Order} {own contra : List PriceLevel} {trades : List Trade}
    {tm : Timestamp} (hd : (inc.remainingQty == 0 || inc.status == .cancelled) = true) :
    dm n inc own contra trades tm = term inc own contra trades tm := by
  cases n with
  | zero => rfl
  | succ n => unfold dm term; rw [doMatch.eq_2, if_pos hd]

theorem rest_done {inc : Order} {own contra : List PriceLevel} {trades : List Trade}
    {tm : Timestamp} (hd : (inc.remainingQty == 0 || inc.status == .cancelled) = true) :
    rest inc own contra trades tm = term inc own contra trades tm := dm_done hd

theorem rest_empty {inc : Order} {own : List PriceLevel} {trades : List Trade} {tm : Timestamp}
    (hd : (inc.remainingQty == 0 || inc.status == .cancelled) = false) :
    rest inc own [] trades tm = term inc own [] trades tm := by
  unfold rest dm term
  rw [doMatch.eq_2, if_neg (by simp [hd])]
  cases hs : inc.side <;> simp [bidsOf, asksOf, hs]

theorem rest_noprice {inc : Order} {own : List PriceLevel} {level : PriceLevel}
    {rl : List PriceLevel} {trades : List Trade} {tm : Timestamp}
    (hd : (inc.remainingQty == 0 || inc.status == .cancelled) = false)
    (hp : canMatchPrice inc level.price = false) :
    rest inc own (level :: rl) trades tm = term inc own (level :: rl) trades tm := by
  unfold rest dm term
  rw [doMatch.eq_2, if_neg (by simp [hd])]
  cases hs : inc.side <;> simp [bidsOf, asksOf, hs, hp]

-- ============================================================================
-- One step per branch
-- ============================================================================

/-- The contra side after the head order of the head level leaves. -/
def drop1 (level : PriceLevel) (restOrders : List Order) (rl : List PriceLevel) : List PriceLevel :=
  if restOrders = [] then rl else { price := level.price, orders := restOrders } :: rl

section Steps

variable {n : Nat} {inc : Order} {own : List PriceLevel} {level : PriceLevel}
  {rl : List PriceLevel} {resting : Order} {restOrders : List Order} {trades : List Trade}
  {tm : Timestamp}

/-- Hypotheses common to every non-terminal step at the head order. -/
structure AtHead (inc : Order) (level : PriceLevel) (resting : Order) (restOrders : List Order) :
    Prop where
  notDone : (inc.remainingQty == 0 || inc.status == .cancelled) = false
  price : canMatchPrice inc level.price = true
  head : level.orders = resting :: restOrders
  visible : resting.visibleQty ≠ 0
  noIceberg : resting.displayQty = none

theorem AtHead.rem (h : AtHead inc level resting restOrders) : inc.remainingQty ≠ 0 := by
  intro e; have := h.notDone; simp [e] at this

theorem AtHead.notCancelled (h : AtHead inc level resting restOrders) :
    inc.status ≠ .cancelled := by
  intro e; have h2 := h.notDone; rw [e, Bool.or_eq_false_iff] at h2; exact absurd h2.2 (by decide)

theorem step_cancelNew (hA : AtHead inc level resting restOrders)
    (hc : selfTradeConflict inc resting = true)
    (hp : inc.stpPolicy.getD .cancelNewest = .cancelNewest) :
    ∀ n, dm (n + 1) inc own (level :: rl) trades tm =
      dm n { inc with status := .cancelled } own (level :: rl) trades tm := by
  intro n
  rw [dm_done (n := n) (inc := { inc with status := .cancelled }) (done_of_cancelled rfl)]
  unfold dm term
  cases hs : inc.side <;>
  · simp only [doMatch, bidsOf, asksOf, hs, hA.head, hA.price]
    simp [hA.notDone, hA.visible, hc, hp]

theorem step_cancelOld (hA : AtHead inc level resting restOrders)
    (hc : selfTradeConflict inc resting = true)
    (hp : inc.stpPolicy.getD .cancelNewest = .cancelOldest) :
    ∀ n, dm (n + 1) inc own (level :: rl) trades tm =
      dm n inc own (drop1 level restOrders rl) trades tm := by
  intro n
  unfold dm drop1
  cases hs : inc.side <;>
  · simp only [doMatch, bidsOf, asksOf, hs, hA.head, hA.price]
    simp [hA.notDone, hA.visible, hc, hp]

theorem step_cancelBoth (hA : AtHead inc level resting restOrders)
    (hc : selfTradeConflict inc resting = true)
    (hp : inc.stpPolicy.getD .cancelNewest = .cancelBoth) :
    ∀ n, dm (n + 1) inc own (level :: rl) trades tm =
      dm n { inc with status := .cancelled } own (drop1 level restOrders rl) trades tm := by
  intro n
  rw [dm_done (n := n) (inc := { inc with status := .cancelled }) (done_of_cancelled rfl)]
  unfold dm term drop1
  cases hs : inc.side <;>
  · simp only [doMatch, bidsOf, asksOf, hs, hA.head, hA.price]
    simp [hA.notDone, hA.visible, hc, hp]

/-- The incoming order after an STP decrement of `q`. -/
def decInc (inc : Order) (q : Nat) : Order :=
  { inc with remainingQty := inc.remainingQty - q,
             status := if inc.remainingQty - q = 0 then .cancelled else inc.status }

theorem step_decrement_full (hA : AtHead inc level resting restOrders)
    (hc : selfTradeConflict inc resting = true)
    (hp : inc.stpPolicy.getD .cancelNewest = .decrement)
    (hfull : resting.remainingQty - min inc.remainingQty resting.visibleQty = 0) :
    ∀ n, dm (n + 1) inc own (level :: rl) trades tm =
      dm n (decInc inc (min inc.remainingQty resting.visibleQty)) own
        (drop1 level restOrders rl) trades tm := by
  have hr := hA.rem
  have hv := hA.visible
  intro n
  unfold dm drop1 decInc
  cases hs : inc.side <;>
  · simp only [doMatch, bidsOf, asksOf, hs, hA.head, hA.price]
    simp [hA.notDone, hc, hp, hfull, hr, hv]

theorem step_decrement_part (hA : AtHead inc level resting restOrders)
    (hc : selfTradeConflict inc resting = true)
    (hp : inc.stpPolicy.getD .cancelNewest = .decrement)
    (hpart : resting.remainingQty - min inc.remainingQty resting.visibleQty ≠ 0) :
    ∀ n, dm (n + 1) inc own (level :: rl) trades tm =
      dm n (decInc inc (min inc.remainingQty resting.visibleQty)) own
        ({ price := level.price, orders :=
            { resting with
              remainingQty := resting.remainingQty - min inc.remainingQty resting.visibleQty,
              visibleQty := resting.visibleQty - min inc.remainingQty resting.visibleQty } ::
              restOrders } :: rl) trades tm := by
  have hr := hA.rem
  have hv := hA.visible
  intro n
  unfold dm decInc
  cases hs : inc.side <;>
  · simp only [doMatch, bidsOf, asksOf, hs, hA.head, hA.price]
    simp [hA.notDone, hc, hp, hpart, hr, hv, hA.noIceberg]

/-- The trade of a fill of `q` against `resting` at `level`. -/
def fillTrade (inc : Order) (level : PriceLevel) (resting : Order) (q : Nat) : Trade :=
  { price := level.price, qty := q, aggressorId := inc.id, passiveId := resting.id,
    aggressorSide := inc.side, aggPostOnly := inc.postOnly, aggStpGroup := inc.stpGroup,
    pasStpGroup := resting.stpGroup, aggStpPolicy := inc.stpPolicy }

theorem step_fill_full (hA : AtHead inc level resting restOrders)
    (hc : selfTradeConflict inc resting = false)
    (hfull : resting.remainingQty - min inc.remainingQty resting.visibleQty = 0) :
    ∀ n, dm (n + 1) inc own (level :: rl) trades tm =
      dm n { inc with remainingQty := inc.remainingQty - min inc.remainingQty resting.visibleQty }
        own (drop1 level restOrders rl)
        (trades ++ [fillTrade inc level resting (min inc.remainingQty resting.visibleQty)]) tm := by
  have hr := hA.rem
  have hv := hA.visible
  intro n
  unfold dm drop1 fillTrade
  cases hs : inc.side <;>
  · simp only [doMatch, bidsOf, asksOf, hs, hA.head, hA.price]
    simp [hA.notDone, hc, hfull, hr, hv]

theorem step_fill_part (hA : AtHead inc level resting restOrders)
    (hc : selfTradeConflict inc resting = false)
    (hpart : resting.remainingQty - min inc.remainingQty resting.visibleQty ≠ 0) :
    ∀ n, dm (n + 1) inc own (level :: rl) trades tm =
      dm n { inc with remainingQty := inc.remainingQty - min inc.remainingQty resting.visibleQty }
        own ({ price := level.price, orders :=
            { resting with
              remainingQty := resting.remainingQty - min inc.remainingQty resting.visibleQty,
              visibleQty := resting.visibleQty - min inc.remainingQty resting.visibleQty,
              status := .partiallyFilled } :: restOrders } :: rl)
        (trades ++ [fillTrade inc level resting (min inc.remainingQty resting.visibleQty)]) tm := by
  have hr := hA.rem
  have hv := hA.visible
  intro n
  unfold dm fillTrade
  cases hs : inc.side <;>
  · simp only [doMatch, bidsOf, asksOf, hs, hA.head, hA.price]
    simp [hA.notDone, hc, hpart, hr, hv, hA.noIceberg]

-- The measure goes down on every step.

theorem mm_drop1 (hq : level.orders = resting :: restOrders) (i i' : Order) :
    matchMeasure (drop1 level restOrders rl) i < matchMeasure (level :: rl) i' := by
  unfold matchMeasure drop1
  exact mm_drop' hq (Nat.lt_succ_self _)

theorem mm_head (hq : level.orders = resting :: restOrders) (r' : Order)
    (hlt : r'.remainingQty < resting.remainingQty) (i i' : Order) :
    matchMeasure ({ price := level.price, orders := r' :: restOrders } :: rl) i <
      matchMeasure (level :: rl) i' := by
  unfold matchMeasure
  exact mm_mod' (newQ := r' :: restOrders) (by rw [hq]; rfl)
    (by rw [hq]; show r'.remainingQty + orderSum restOrders < resting.remainingQty + orderSum restOrders
        exact Nat.add_lt_add_right hlt _) (Nat.lt_succ_self _)

end Steps

-- ============================================================================
-- The accepted-order pipeline on a stop-free book
-- ============================================================================

theorem processCascade_nostops : ∀ (f : Nat) (ts : List Trade) (b : BookState), b.stops = [] →
    (processCascade f ts b).trades = [] ∧ (processCascade f ts b).book.bids = b.bids ∧
      (processCascade f ts b).book.asks = b.asks ∧ (processCascade f ts b).book.stops = b.stops
  | 0, _, b, _ => by simp [processCascade]
  | _ + 1, [], b, _ => by simp [processCascade]
  | f + 1, t :: ts, b, hs => by
    have ih := processCascade_nostops f ts { b with lastTradePrice := some t.price } hs
    have hp : List.partition (fun s => shouldTrigger s (some t.price)) [] = ([], []) := rfl
    simp only [processCascade, hs, hp, List.isEmpty_nil, if_true]
    simp only [hs] at ih
    exact ih

/-- The spec order `process` hands to `processOrder`. -/
def o1Of (b : BookState) (o : Order) : Order := { o with id := o.id, timestamp := b.clock }

/-- The spec's matching run for an accepted order. -/
def mrOf (b : BookState) (o : Order) : MatchResult :=
  doMatch (computeMatchFuel b o.side) (o1Of b o) b.bids b.asks [] (b.clock + 1)

/-- The book `dispose` receives. -/
def afterMatch (b : BookState) (o : Order) : BookState :=
  { ({ b with nextId := o.id } : BookState) with
    bids := (mrOf b o).bids, asks := (mrOf b o).asks, clock := (mrOf b o).clock }

/-- **Accepted, not post-only**: `processWithId` is `doMatch`, then `dispose`,
    as seen through `bookView`, and its trades are `doMatch`'s. -/
theorem processWithId_match {b : BookState} {o : Order} (hstops : b.stops = [])
    (hns : o.orderType ≠ .stopLimit ∧ o.orderType ≠ .stopMarket) (hfok : o.tif ≠ .fok)
    (hmq : o.minQty = none) (hmtl : o.orderType ≠ .marketToLimit) (hpo : o.postOnly = false) :
    (processWithId b o).trades = (mrOf b o).trades ∧
    bookView (processWithId b o).book =
      bookView (dispose (mrOf b o).incoming (afterMatch b o) (mrOf b o).trades) := by
  obtain ⟨k, hk⟩ : ∃ k, computeProcessFuel { b with nextId := o.id } (o1Of b o) = k + 1 :=
    ⟨_, rfl⟩
  have hns' : (o.orderType == OrderType.stopLimit || o.orderType == OrderType.stopMarket) = false := by
    cases ht : o.orderType <;> first | rfl | exact absurd ht hns.1 | exact absurd ht hns.2
  have hfok' : (o.tif == TimeInForce.fok) = false := by
    cases ht : o.tif <;> first | rfl | exact absurd ht hfok
  have hmtl' : (o.orderType == OrderType.marketToLimit) = false := by
    cases ht : o.orderType <;> first | rfl | exact absurd ht hmtl
  unfold processWithId process
  simp only
  simp only [o1Of] at hk
  rw [hk, processOrder.eq_2]
  simp only [o1Of, hns', hpo, hfok', hmq, hmtl', Bool.false_eq_true, if_false, Option.isSome_none,
    Bool.false_and]
  generalize hM : matchOrder _ _ _ = M
  have hMe : M = mrOf b o := by
    rw [← hM]; cases o; simp_all [matchOrder, mrOf, o1Of, computeMatchFuel, contraLevels]
  subst hMe
  generalize hB : dispose (mrOf b o).incoming _ (mrOf b o).trades = B
  have hBe : B = dispose (mrOf b o).incoming (afterMatch b o) (mrOf b o).trades := by
    rw [← hB]; rfl
  have hBs : B.stops = [] := by
    rw [hBe]; unfold dispose
    split
    · exact hstops
    · split
      · exact hstops
      · split
        · exact hstops
        · rw [insertOrder_preserves_stops]; exact hstops
  have hc := fun ltp => processCascade_nostops k (mrOf b o).trades { B with lastTradePrice := ltp } hBs
  rw [← hBe]
  refine ⟨?_, ?_⟩
  · rw [(hc _).1]; simp
  · simp only [bookView, (hc _).2.1, (hc _).2.2.1, (hc _).2.2.2]

theorem computeMatchFuel_pos (b : BookState) (s : Side) : ∃ k, computeMatchFuel b s = k + 1 :=
  ⟨_, rfl⟩

/-- **Accepted post-only** (it does not cross): the spec's matching run is
    empty, and `processWithId` rests the order, which is what `dispose` does
    with the empty run. Same shape as `processWithId_match`. -/
theorem processWithId_postOnly {b : BookState} {o : Order} (hstops : b.stops = [])
    (hns : o.orderType ≠ .stopLimit ∧ o.orderType ≠ .stopMarket) (hpo : o.postOnly = true)
    (hwc : wouldCross (o1Of b o) { b with nextId := o.id } = false)
    (hrem : o.remainingQty ≠ 0) (hst : o.status = .new_) (htif : o.tif = .gtc)
    (hty : o.orderType = .limit) (hpx : ∃ p, o.price = some p) :
    (processWithId b o).trades = (mrOf b o).trades ∧
    bookView (processWithId b o).book =
      bookView (dispose (mrOf b o).incoming (afterMatch b o) (mrOf b o).trades) := by
  obtain ⟨p, hp⟩ := hpx
  -- the spec's matching run is empty
  have hmr : mrOf b o = { incoming := o1Of b o, bids := b.bids, asks := b.asks, trades := [], clock := b.clock + 1 } := by
    obtain ⟨k, hk⟩ := computeMatchFuel_pos b o.side
    unfold mrOf
    rw [hk, doMatch.eq_2]
    have hne : (OrderStatus.new_ == OrderStatus.cancelled) = false := by decide
    have hnd : ((o1Of b o).remainingQty == 0 || (o1Of b o).status == .cancelled) = false := by
      simp [o1Of, hrem, hst, hne]
    rw [if_neg (by simp [hnd])]
    unfold wouldCross bestAskPrice bestBidPrice at hwc
    simp only [o1Of, hp] at hwc
    cases hs : o.side
    · rw [hs] at hwc
      cases ha : b.asks with
      | nil => simp [o1Of, hs, ha]
      | cons l ls =>
        rw [ha] at hwc
        simp at hwc
        simp [o1Of, hs, ha, canMatchPrice, hp]; omega
    · rw [hs] at hwc
      cases hb : b.bids with
      | nil => simp [o1Of, hs, hb]
      | cons l ls =>
        rw [hb] at hwc
        simp at hwc
        simp [o1Of, hs, hb, canMatchPrice, hp]; omega
  -- process rests the order
  obtain ⟨k, hk⟩ : ∃ k, computeProcessFuel { b with nextId := o.id } (o1Of b o) = k + 1 :=
    ⟨_, rfl⟩
  have hns' : (o.orderType == OrderType.stopLimit || o.orderType == OrderType.stopMarket) = false := by
    cases ht : o.orderType <;> first | rfl | exact absurd ht hns.1 | exact absurd ht hns.2
  have hproc : processWithId b o = { book := { insertOrder { b with nextId := o.id } (o1Of b o) false with nextId := o.id + 1, clock := Nat.max (insertOrder { b with nextId := o.id } (o1Of b o) false).clock (b.clock + 1) }, trades := [] } := by
    obtain ⟨oid, os, ot, otif, opx, ostop, oq, orem, omq, odq, ovq, opo, ost, ots, og, opol⟩ := o
    simp only at hpo
    subst hpo
    unfold processWithId process
    simp only [o1Of] at hk hwc ⊢
    rw [hk, processOrder.eq_2]
    simp only at hns'
    simp only [hns', Bool.false_eq_true, if_false, if_true, hwc]
  rw [hproc, hmr]
  refine ⟨rfl, ?_⟩
  have hne : (OrderStatus.new_ == OrderStatus.cancelled) = false := by decide
  have hd : dispose (o1Of b o) (afterMatch b o) [] = insertOrder (afterMatch b o) (o1Of b o) false := by
    unfold dispose
    have h1 : (TimeInForce.gtc == TimeInForce.ioc) = false := by decide
    have h2 : (OrderType.limit == OrderType.market) = false := by decide
    simp [o1Of, hrem, hst, htif, hty, hne, h1, h2]
  simp only at hd ⊢
  rw [hd]
  have hab : (afterMatch b o).bids = b.bids ∧ (afterMatch b o).asks = b.asks := by
    unfold afterMatch; rw [hmr]; exact ⟨rfl, rfl⟩
  unfold insertOrder
  cases hs : (o1Of b o).side <;>
    simp [bookView, afterMatch, hmr]

end MatcherSpec
