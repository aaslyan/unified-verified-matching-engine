import MatchingEngine.Process
import MatchingEngine.Invariants
import MatchingEngine.Theorems
import MatchingEngine.TheoremsFull

/-!
# Reachable-State Corollary

`process_preserves_BookInvariant` (`TheoremsFull.lean`) is a **single-step**
theorem: if a book already satisfies a precondition bundle, then after
processing one order, `BookInvariant` holds for the result. The paper's
headline claim is stronger — that `BookInvariant` holds for *every* book
reachable from the empty book via an arbitrary sequence of well-formed
orders.

The composition needs a *loop invariant*: a predicate bundle strong enough
that (a) the empty book satisfies it, and (b) if it holds before processing
one more order, it still holds after. `process_preserves_BookInvariant`'s own
hypotheses (`AllInv`, `BookOk`, `StopsWF`) are exactly that bundle, plus
`StopsNoPostOnly` (needed to re-invoke `AllInv` preservation on the next
step). Call it `ProcessInv`.

## Status

- `AllInv_empty`, `StopsNoPostOnly_empty`, `ProcessInv_empty` — PROVED (the
  empty book trivially satisfies the bundle).
- `process_preserves_AllInv`, `process_preserves_StopsNoPostOnly` — PROVED in `Theorems.lean`.
- `ProcessInv_step`, `ProcessInv_foldl` — PROVED by list induction.
- `BookInvariant_of_ProcessInv` — PROVED: `ProcessInv` implies `BookInvariant`.
- `process_all_preserves_BookInvariant` — PROVED: for any sequence of orders
  satisfying `OrderProcOk ∧ OrderRestOk`, the reachable book satisfies `BookInvariant`.
- `OrderProcOk_of_WellFormed`, `reachable_BookInvariant` — PROVED: the same
  result with the hypothesis stated as `Order.WellFormed`.
- `reachable_all_invariants`, `reachable_all_invariants_prefix` — PROVED:
  along any well-formed run, the book satisfies `BookInvariant` at every
  prefix, and every emitted trade satisfies INV-11 and INV-12.

These are safety results. Completeness of each step (no stop dropped by
fuel exhaustion) is `processOrder_computeProcessFuel_stable` in
`TheoremsFuel.lean`.
-/

/-- Fold-friendly form of `process`: just the resulting book, discarding the
    emitted trades. -/
def processBook (b : BookState) (o : Order) : BookState := (process b o).book

/-- The loop invariant: the precondition bundle needed to invoke
    `process_preserves_BookInvariant` again on the *next* order. -/
def ProcessInv (b : BookState) : Prop :=
  AllInv b ∧ BookOk b ∧ StopsWF b ∧ StopsNoPostOnly b

theorem AllInv_empty : AllInv BookState.empty :=
  ⟨BookUncrossed_no_asks BookState.empty rfl, rfl, rfl⟩

theorem StopsNoPostOnly_empty : StopsNoPostOnly BookState.empty := by
  intro s hs
  cases hs

/-- The empty book satisfies the loop invariant (base case). -/
theorem ProcessInv_empty : ProcessInv BookState.empty :=
  ⟨AllInv_empty, BookOk_empty, StopsWF_empty, StopsNoPostOnly_empty⟩

/-- The loop invariant is preserved by one call to `process` (inductive
    step). -/
theorem ProcessInv_step (b : BookState) (o : Order)
    (hinv : ProcessInv b) (hpok : OrderProcOk o) (hok : OrderRestOk o) :
    ProcessInv (process b o).book := by
  obtain ⟨hall, hb, hstopsWF, hsnp⟩ := hinv
  exact ⟨process_preserves_AllInv b o hpok hsnp hall,
    (process_preserves_BookOk b o hb hstopsWF hok).1,
    (process_preserves_BookOk b o hb hstopsWF hok).2,
    process_preserves_StopsNoPostOnly b o hpok hsnp hall⟩

/-- The loop invariant survives folding `process` over any list of orders
    that are individually well-formed enough to invoke `process`. Proved
    by list induction. -/
theorem ProcessInv_foldl (orders : List Order) (b : BookState)
    (hinv : ProcessInv b)
    (hwf : ∀ o ∈ orders, OrderProcOk o ∧ OrderRestOk o) :
    ProcessInv (orders.foldl processBook b) := by
  induction orders generalizing b with
  | nil => exact hinv
  | cons o rest ih =>
    have ho := hwf o List.mem_cons_self
    have hstep : ProcessInv (processBook b o) :=
      ProcessInv_step b o hinv ho.1 ho.2
    have hrest : ∀ o' ∈ rest, OrderProcOk o' ∧ OrderRestOk o' :=
      fun o' hmem => hwf o' (List.mem_cons_of_mem o hmem)
    exact ih (processBook b o) hstep hrest

/-- Every state satisfying the loop invariant `ProcessInv` also satisfies the
    full §13 `BookInvariant`. -/
theorem BookInvariant_of_ProcessInv {b : BookState} (hinv : ProcessInv b) :
    BookInvariant b := by
  obtain ⟨hall, hb, -, -⟩ := hinv
  obtain ⟨hne, hng, hsc, hfifo, hnm, hnmtl, hnmq⟩ := FullBookInv_of_BookOkAt hb
  exact ⟨hall.1, hng, hsc, hnm, hnmtl, hnmq, hne, hfifo⟩

/-- **The reachable-state corollary.** For any finite sequence of orders that
    are each well-formed enough to invoke `process` (`OrderProcOk`,
    `OrderRestOk` — both implied by `Order.WellFormed`, see
    `OrderRestOk_of_WellFormed` and `OrderProcOk_of_WellFormed`), the book
    reached by processing them one at a time from the empty book satisfies
    the full §13 `BookInvariant`. -/
theorem process_all_preserves_BookInvariant (orders : List Order)
    (hwf : ∀ o ∈ orders, OrderProcOk o ∧ OrderRestOk o) :
    BookInvariant (orders.foldl processBook BookState.empty) :=
  BookInvariant_of_ProcessInv (ProcessInv_foldl orders BookState.empty ProcessInv_empty hwf)

/-- `OrderProcOk` follows from `Order.WellFormed`: a post-only order is a
    LIMIT order (WF-16), a LIMIT order carries a price (WF-2), and hence a
    stop order cannot be post-only. -/
theorem OrderProcOk_of_WellFormed {o : Order} (h : o.WellFormed) : OrderProcOk o := by
  unfold Order.WellFormed at h
  obtain ⟨-, hlim, -, -, -, -, -, -, -, -, -, -, -, -, -, hpo, -, -, -, -, -, -, -, -⟩ := h
  refine ⟨fun hp => (hlim (hpo hp)).1, fun hstop => ?_⟩
  cases hp : o.postOnly with
  | false => rfl
  | true =>
    have hl := hpo hp
    rcases hstop with hs | hs <;> rw [hs] at hl <;> cases hl

/-- The reachable-state corollary with the hypothesis stated directly as
    `Order.WellFormed`. -/
theorem reachable_BookInvariant (orders : List Order)
    (hwf : ∀ o ∈ orders, o.WellFormed) :
    BookInvariant (orders.foldl processBook BookState.empty) :=
  process_all_preserves_BookInvariant orders
    (fun o ho => ⟨OrderProcOk_of_WellFormed (hwf o ho), OrderRestOk_of_WellFormed (hwf o ho)⟩)

/-- Run a sequence of orders, keeping the final book and every emitted trade. -/
def runFrom (b : BookState) : List Order → BookState × List Trade
  | [] => (b, [])
  | o :: os =>
    let r := process b o
    let s := runFrom r.book os
    (s.1, r.trades ++ s.2)

theorem runFrom_book (b : BookState) (orders : List Order) :
    (runFrom b orders).1 = orders.foldl processBook b := by
  induction orders generalizing b with
  | nil => rfl
  | cons o os ih => exact ih _

theorem runFrom_TradesOk (b : BookState) (orders : List Order) :
    TradesOk (runFrom b orders).2 := by
  induction orders generalizing b with
  | nil => intro t ht; cases ht
  | cons o os ih =>
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact process_emits_safe_trades b o t h
    · exact ih _ t h

/-- **Every §13 invariant along every well-formed run.** Starting from the
    empty book and processing any finite sequence of well-formed orders:

    * the resulting book satisfies the full `BookInvariant` (INV-1..INV-10,
      INV-13, INV-14), and
    * every trade emitted anywhere in the run satisfies the post-only
      (INV-11) and STP (INV-12) guarantees.

    Because any prefix of a well-formed sequence is well-formed, the same
    holds at every intermediate state (`reachable_all_invariants_prefix`).
    The stop cascade inside each step is not truncated by fuel
    (`processOrder_computeProcessFuel_stable` in `TheoremsFuel.lean`). -/
theorem reachable_all_invariants (orders : List Order)
    (hwf : ∀ o ∈ orders, o.WellFormed) :
    BookInvariant (runFrom BookState.empty orders).1 ∧
    PostOnlyGuarantee (runFrom BookState.empty orders).2 ∧
    STPGuarantee (runFrom BookState.empty orders).2 := by
  refine ⟨?_, fun t ht => (runFrom_TradesOk _ _ t ht).1,
    fun t ht => (runFrom_TradesOk _ _ t ht).2⟩
  rw [runFrom_book]
  exact reachable_BookInvariant orders hwf

theorem reachable_all_invariants_prefix (orders : List Order)
    (hwf : ∀ o ∈ orders, o.WellFormed) (k : Nat) :
    BookInvariant (runFrom BookState.empty (orders.take k)).1 ∧
    PostOnlyGuarantee (runFrom BookState.empty (orders.take k)).2 ∧
    STPGuarantee (runFrom BookState.empty (orders.take k)).2 :=
  reachable_all_invariants _ (fun o ho => hwf o (List.mem_of_mem_take ho))
