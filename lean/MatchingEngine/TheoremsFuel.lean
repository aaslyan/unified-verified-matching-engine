import MatchingEngine.Process
import MatchingEngine.Theorems
import MatchingEngine.TheoremsFull

/-!
# Outer Fuel Sufficiency

`process` runs the mutually recursive stop-cascade workers with
`computeProcessFuel`. The invariant theorems hold for any fuel, so they do
not show that this budget is large enough. When fuel runs out, triggered
stops that were already removed from `b.stops` are silently dropped, and
the book is still well-formed.

This file proves the budget is never binding
(`processOrder_computeProcessFuel_stable`). The argument:

- `doMatch_tradeBudget_le`: each fill consumes at least one unit of the
  incoming order, so a match emits at most `remainingQty` trades.
- `process_all_stops_sublist`: processing a non-stop order only removes
  dormant stops, so every level of cascade nesting consumes one.
- `process_all_fuel_stable`: with `needOrder`, `needCascade` and
  `needTriggered` fuel (linear in incoming quantity plus dormant-stop
  weight), any larger fuel gives the identical result.
- `needOrder_le_computeProcessFuel`: the quadratic budget dominates the need.
-/

/-- Trades emitted plus quantity the incoming order still has left. -/
def tradeBudget (r : MatchResult) : Nat := r.trades.length + r.incoming.remainingQty

private theorem fill_budget (a q v : Nat) (hq : ¬q = 0) (hv : ¬v = 0) :
    a + 1 + (q - min q v) ≤ a + q := by omega

/-- Each fill consumes at least one unit of the incoming order, so the number
    of new trades plus the leftover quantity never exceeds what it started with. -/
theorem doMatch_tradeBudget_le (fuel : Nat) (inc : Order) (bids asks : List PriceLevel)
    (trades : List Trade) (tm : Timestamp) :
    tradeBudget (doMatch fuel inc bids asks trades tm) ≤
      trades.length + inc.remainingQty := by
  fun_induction doMatch fuel inc bids asks trades tm
  all_goals first
    | exact Nat.le_refl _
    | (rename_i ih; exact ih)
    | (rename_i ih; exact Nat.le_trans ih (Nat.add_le_add_left (Nat.sub_le _ _) _))
    | (rename_i ih; refine Nat.le_trans ih ?_; clear ih; simp_all (config := {zetaDelta := true}) <;>
        exact fill_budget _ _ _ (‹¬ _ = 0 ∧ _›).1 ‹_›)

/-- The Phase 1 stop test of `processOrder`. -/
def isStopT (o : Order) : Bool :=
  o.orderType == .stopLimit || o.orderType == .stopMarket

theorem convertStop_isStopT (s : Order) (t : Timestamp) :
    isStopT (convertStop s t) = false := by
  unfold convertStop isStopT
  split
  · rfl
  · rfl
  · rename_i h1 h2
    cases hv : s.orderType <;> simp_all <;> decide

/-- Processing a non-stop order never adds dormant stops. -/
theorem process_all_stops_sublist : ∀ (fuel : Nat),
    (∀ (o : Order) (b : BookState), isStopT o = false →
      (processOrder fuel o b).book.stops.Sublist b.stops) ∧
    (∀ (trades : List Trade) (b : BookState),
      (processCascade fuel trades b).book.stops.Sublist b.stops) ∧
    (∀ (orders : List Order) (b : BookState),
      (processTriggeredStops fuel orders b).book.stops.Sublist b.stops) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro o b _; exact List.Sublist.refl _
    · intro ts b; cases ts <;> exact List.Sublist.refl _
    · intro os b; cases os <;> exact List.Sublist.refl _
  | succ n ih =>
    obtain ⟨ih_po, ih_pc, ih_pts⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro o b hns
      unfold processOrder
      simp only
      split
      · rename_i hstop
        exact absurd hstop (by simpa [isStopT] using hns)
      · split
        · split
          · exact List.Sublist.refl _
          · rw [insertOrder_preserves_stops]; exact List.Sublist.refl _
        · split
          · split
            · exact List.Sublist.refl _
            · exact ih_pc _ _
          · split
            · exact List.Sublist.refl _
            · split
              · split
                · exact List.Sublist.refl _
                · split
                  · exact ih_pc _ _
                  · exact (ih_pc _ _).trans
                      (by rw [dispose_preserves_stops]; exact List.Sublist.refl _)
              · exact (ih_pc _ _).trans
                  (by rw [dispose_preserves_stops]; exact List.Sublist.refl _)
    · intro ts b
      unfold processCascade
      match ts with
      | [] => exact List.Sublist.refl _
      | t :: rest =>
        simp only
        split
        · exact ih_pc _ _
        · exact ((ih_pc _ _).trans (ih_pts _ _)).trans (by simp only [List.partition_eq_filter_filter]; exact List.filter_sublist)
    · intro os b
      unfold processTriggeredStops
      match os with
      | [] => exact List.Sublist.refl _
      | stop :: rest =>
        simp only
        exact (ih_pts _ _).trans (ih_po _ _ (convertStop_isStopT _ _))

/-- Weight of a stop list: one unit per stop plus its remaining quantity. -/
def stopW (l : List Order) : Nat := (l.map (fun o => o.remainingQty + 1)).sum

theorem stopW_cons (s : Order) (l : List Order) :
    stopW (s :: l) = s.remainingQty + 1 + stopW l := by
  simp [stopW]

theorem stopW_sublist {l₁ l₂ : List Order} (h : l₁.Sublist l₂) : stopW l₁ ≤ stopW l₂ := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a _ ih => rw [stopW_cons]; omega
  | cons₂ a _ ih => rw [stopW_cons, stopW_cons]; omega

theorem stopW_partition (p : Order → Bool) (l : List Order) :
    stopW (l.partition p).1 + stopW (l.partition p).2 = stopW l := by
  simp only [List.partition_eq_filter_filter]
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hp : p a = true
    · simp [hp, stopW_cons]; omega
    · simp [hp, stopW_cons]; omega

theorem stopW_mergeSort (l : List Order) (le : Order → Order → Bool) :
    stopW (l.mergeSort le) = stopW l := by
  unfold stopW
  exact ((List.mergeSort_perm l le).map _).sum_nat

theorem stopW_pos {l : List Order} (h : ¬l.isEmpty = true) : 1 ≤ stopW l := by
  cases l with
  | nil => simp at h
  | cons s l => rw [stopW_cons]; omega

theorem matchOrder_budget (f : Nat) (b : BookState) (o : Order) :
    (matchOrder f b o).trades.length + (matchOrder f b o).incoming.remainingQty ≤
      o.remainingQty := by
  have := doMatch_tradeBudget_le f o b.bids b.asks [] (b.clock + 1)
  simpa [tradeBudget, matchOrder] using this

theorem doMatch_trades_length_le (f : Nat) (inc : Order) (bids asks : List PriceLevel)
    (tm : Timestamp) :
    (doMatch f inc bids asks [] tm).trades.length ≤ inc.remainingQty := by
  have := doMatch_tradeBudget_le f inc bids asks [] tm
  unfold tradeBudget at this
  simp at this
  omega

/-- Fuel that each of the three workers provably needs. -/
def needOrder (o : Order) (b : BookState) : Nat :=
  o.remainingQty + 1 + 4 * stopW b.stops + (if isStopT o then 1 else 0)

def needCascade (ts : List Trade) (b : BookState) : Nat :=
  ts.length + 4 * stopW b.stops

def needTriggered (l : List Order) (b : BookState) : Nat :=
  stopW l + 2 + 4 * stopW b.stops

/-- Once the fuel reaches the need, adding more fuel changes nothing. -/
theorem process_all_fuel_stable : ∀ (n : Nat),
    (∀ (o : Order) (b : BookState), needOrder o b ≤ n →
      ∀ m, n ≤ m → processOrder m o b = processOrder n o b) ∧
    (∀ (ts : List Trade) (b : BookState), needCascade ts b ≤ n →
      ∀ m, n ≤ m → processCascade m ts b = processCascade n ts b) ∧
    (∀ (l : List Order) (b : BookState), needTriggered l b ≤ n →
      ∀ m, n ≤ m → processTriggeredStops m l b = processTriggeredStops n l b) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro o b h; unfold needOrder at h; omega
    · intro ts b h m _
      unfold needCascade at h
      cases ts with
      | cons t rest => simp at h
      | nil =>
        cases m with
        | zero => rfl
        | succ m => rw [processCascade.eq_2 _ _ (by omega), processCascade.eq_1]
    · intro l b h; unfold needTriggered at h; omega
  | succ n ih =>
    obtain ⟨ih_po, ih_pc, ih_pts⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro o b hneed m hm
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      unfold needOrder at hneed
      rw [processOrder.eq_2, processOrder.eq_2]
      simp only
      split
      · rename_i hstop
        have hs : isStopT o = true := hstop
        rw [hs] at hneed
        simp only [↓reduceIte] at hneed
        split
        · refine ih_po _ _ ?_ m (by omega)
          unfold needOrder
          rw [convertStop_isStopT, convertStop_remainingQty]
          simp only [if_false, Bool.false_eq_true]
          omega
        · rfl
      · rename_i hstop
        have hs : isStopT o = false := by simpa [isStopT] using hstop
        rw [hs] at hneed
        simp only [if_false, Bool.false_eq_true] at hneed
        have hmo := matchOrder_budget (computeMatchFuel b o.side) b o
        split
        · split <;> rfl
        · split
          · split
            · rfl
            · rw [ih_pc _ _ ?_ m (by omega)]
              unfold needCascade; simp only; omega
          · split
            · rfl
            · split
              · split
                · rfl
                · split
                  · rw [ih_pc _ _ ?_ m (by omega)]
                    unfold needCascade; simp only; omega
                  · rw [ih_pc _ _ ?_ m (by omega)]
                    unfold needCascade
                    simp only [dispose_preserves_stops, List.length_append]
                    have h2 := doMatch_trades_length_le
                      (computeMatchFuel
                        { b with bids := (matchOrder (computeMatchFuel b o.side) b o).bids,
                                 asks := (matchOrder (computeMatchFuel b o.side) b o).asks,
                                 clock := (matchOrder (computeMatchFuel b o.side) b o).clock }
                        (matchOrder (computeMatchFuel b o.side) b o).incoming.side)
                      { (matchOrder (computeMatchFuel b o.side) b o).incoming with
                        orderType := .limit,
                        price := some (matchOrder (computeMatchFuel b o.side) b o).trades.head!.price,
                        minQty := none }
                      (matchOrder (computeMatchFuel b o.side) b o).bids
                      (matchOrder (computeMatchFuel b o.side) b o).asks
                      (matchOrder (computeMatchFuel b o.side) b o).clock
                    simp only at h2
                    omega
              · rw [ih_pc _ _ ?_ m (by omega)]
                unfold needCascade
                simp only [dispose_preserves_stops]
                omega
    · intro ts b hneed m hm
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      unfold needCascade at hneed
      cases ts with
      | nil =>
        rw [processCascade.eq_2 _ _ (by omega), processCascade.eq_2 _ _ (by omega)]
      | cons t rest =>
        simp only [List.length_cons] at hneed
        rw [processCascade.eq_3, processCascade.eq_3]
        split
        · rename_i tr rem hpart
          have hW := stopW_partition (fun s => shouldTrigger s (some t.price)) b.stops
          rw [hpart] at hW
          simp only at hW
          split
          · exact ih_pc _ _ (by unfold needCascade; simp only; omega) m (by omega)
          · rename_i hne
            have hpos := stopW_pos hne
            simp only
            rw [ih_pts _ _ ?_ m (by omega)]
            · have hsub := (process_all_stops_sublist n).2.2
                (tr.mergeSort fun a c => decide (a.timestamp < c.timestamp))
                { b with stops := rem, lastTradePrice := some t.price }
              have hWs := stopW_sublist hsub
              simp only at hWs
              rw [ih_pc _ _ ?_ m (by omega)]
              unfold needCascade
              omega
            · unfold needTriggered
              rw [stopW_mergeSort]
              simp only
              omega
    · intro l b hneed m hm
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      unfold needTriggered at hneed
      cases l with
      | nil =>
        rw [processTriggeredStops.eq_2 _ _ (by omega), processTriggeredStops.eq_2 _ _ (by omega)]
      | cons s rest =>
        rw [stopW_cons] at hneed
        rw [processTriggeredStops.eq_3, processTriggeredStops.eq_3]
        rw [ih_po _ _ ?_ m (by omega)]
        · have hsub := (process_all_stops_sublist n).1 (convertStop s b.clock)
            { b with clock := b.clock + 1 } (convertStop_isStopT _ _)
          have hWs := stopW_sublist hsub
          simp only at hWs
          rw [ih_pts _ _ ?_ m (by omega)]
          unfold needTriggered
          omega
        · unfold needOrder
          rw [convertStop_isStopT, convertStop_remainingQty]
          simp only [if_false, Bool.false_eq_true]
          omega

theorem stops_foldl_eq (l : List Order) (a : Nat) :
    l.foldl (fun n o => n + o.remainingQty + 1) a = a + stopW l := by
  induction l generalizing a with
  | nil => simp [stopW]
  | cons s l ih => rw [List.foldl_cons, ih, stopW_cons]; omega

theorem needOrder_le_computeProcessFuel (b : BookState) (o : Order) :
    needOrder o b ≤ computeProcessFuel b o := by
  unfold needOrder computeProcessFuel
  simp only [stops_foldl_eq, Nat.zero_add]
  generalize sideProcessMeasure b.bids + sideProcessMeasure b.asks = S
  generalize stopW b.stops = W
  generalize o.remainingQty = q
  have hstop : (if isStopT o = true then 1 else 0) ≤ 1 := by split <;> omega
  have hsq := Nat.mul_le_mul (Nat.le_add_left (W + 1) (S + q))
    (Nat.le_add_left (W + 1) (S + q))
  have hW := Nat.le_mul_self W
  have hexp : (W + 1) * (W + 1) = W * W + 2 * W + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  have hm : S + W + q + 1 = S + q + (W + 1) := by omega
  rw [hm]
  omega

/-- **Outer fuel sufficiency.** `computeProcessFuel` never truncates the
    stop cascade: running `processOrder` with any larger fuel gives exactly
    the same book and trades. So every stop that the cascade triggers is
    processed, and no triggered stop is dropped by fuel exhaustion. -/
theorem processOrder_computeProcessFuel_stable (b : BookState) (o : Order) (m : Nat)
    (hm : computeProcessFuel b o ≤ m) :
    processOrder m o b = processOrder (computeProcessFuel b o) o b :=
  (process_all_fuel_stable (computeProcessFuel b o)).1 o b
    (needOrder_le_computeProcessFuel b o) m hm
