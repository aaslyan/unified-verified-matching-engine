import MatchingEngine
import Bridge.EngineDbAbs

/-!
# `processB`: the spec step the generated matcher must refine

`processB cap b req` wraps the verified spec (`process`, `cancelOrder`) with
the entry checks of plan v2 §4. `process` and its proofs are not edited.

Checks, in order, each leaving the book unchanged and emitting no trade:

1. **Unsupported order type.** The request language is C's `OrderRequest`,
   whose order type is a `uint8_t` code. The supported codes are LIMIT,
   MARKET, IOC and POST_ONLY; every other code, which is where FOK, DAY,
   stops, market-to-limit, iceberg and minimum-quantity orders would be
   encoded, is `rejectedUnsupported`.
2. **Invalid request.** Zero quantity, price 0 on a priced type, side or STP
   mode out of range (`CRequest.toSpec = none`), or quantity above `qmax cap`.
3. **Duplicate id.** The id is already resting.
4. **Capacity.** The request may rest (LIMIT or POST_ONLY) and the book is
   full. Pessimistic by design: an order that would have filled completely
   is also rejected.
5. **Post-only would cross.** The same test `process` applies.

Otherwise the order runs through `processWithId` (`process` with the
caller's id). A cancel runs through `cancelOrder`.

The transfer lemmas: every rejection returns the input book, so it keeps
every invariant trivially; an accepted order uses the existing reachable-state
step; a cancel uses `cancelOrder_preserves_ProcessInv`, proved here because
the spec had no invariant theorem for `cancelOrder`.
-/

namespace ProcessB

open EngineDbApi EngineDbAbs

-- ============================================================================
-- Requests, result codes, observables
-- ============================================================================

/-- A request to the engine: an order, or a cancel by id. -/
inductive Req where
  | order  : CRequest → Req
  | cancel : UInt64 → Req
  deriving Repr

inductive ResultCode where
  | accepted
  | cancelled
  | rejectedUnsupported
  | rejectedInvalid
  | rejectedDuplicate
  | rejectedCapacity
  | rejectedPostOnly
  | rejectedUnknownId
  deriving DecidableEq, Repr

/-- The per-order quantity bound: `(cap + 1) * qmax cap < 2^64`, so the
    per-level totals of at most `cap` resting orders, plus the incoming one,
    fit in `uint64_t` (§4 "Quantity bounds"). -/
def qmax (cap : Nat) : Nat := (2 ^ 64 - 1) / (cap + 1)

theorem qmax_bound (cap : Nat) : (cap + 1) * qmax cap < 2 ^ 64 := by
  unfold qmax
  have := Nat.div_mul_le_self (2 ^ 64 - 1) (cap + 1)
  rw [Nat.mul_comm]
  have h : (2 : Nat) ^ 64 - 1 < 2 ^ 64 := by decide
  omega

/-- Resting orders plus dormant stops: what a store of capacity `cap` holds. -/
def bookSize (b : BookState) : Nat := (allBookOrders b).length + b.stops.length

/-- The id is already on the book. -/
def idOnBook (b : BookState) (id : OrderId) : Bool := (allBookOrders b).any (·.id == id)

/-- The request can leave a resting order: LIMIT (GTC) or POST_ONLY. -/
def requestMayRest (r : CRequest) : Bool :=
  match decodeOrderType r.orderType with
  | some .limit | some .postOnly => true
  | _ => false

def rejectWith (c : ResultCode) (b : BookState) : ResultCode × ProcessResult :=
  (c, { book := b, trades := [] })

/-- The spec step of the generated matcher. -/
def processB (cap : Nat) (b : BookState) : Req → ResultCode × ProcessResult
  | .order r =>
    match decodeOrderType r.orderType with
    | none => rejectWith .rejectedUnsupported b
    | some _ =>
      match r.toSpec with
      | none => rejectWith .rejectedInvalid b
      | some o =>
        if qmax cap < r.qty.toNat then rejectWith .rejectedInvalid b
        else if idOnBook b o.id then rejectWith .rejectedDuplicate b
        else if requestMayRest r && cap ≤ bookSize b then rejectWith .rejectedCapacity b
        else if o.postOnly && wouldCross o b then rejectWith .rejectedPostOnly b
        else (.accepted, processWithId b o)
  | .cancel id =>
    match cancelOrder b id.toNat with
    | none => rejectWith .rejectedUnknownId b
    | some b' => (.cancelled, { book := b', trades := [] })

/-- One trade as the C engine reports it: maker = passive, taker = aggressor. -/
structure TradeObs where
  makerId : Nat
  takerId : Nat
  price   : Nat
  qty     : Nat
  deriving DecidableEq, Repr

def tradeObs (t : Trade) : TradeObs :=
  { makerId := t.passiveId, takerId := t.aggressorId, price := t.price, qty := t.qty }

/-- What the refinement theorem compares: the result code, the trades in
    execution order, and the book restricted to the fields C stores. -/
structure Obs where
  code   : ResultCode
  trades : List TradeObs
  book   : BookView

def obsSpec (x : ResultCode × ProcessResult) : Obs :=
  { code := x.1, trades := x.2.trades.map tradeObs, book := bookView x.2.book }

/-- The matcher's observation: its result code and trade buffer, and the book
    its final store decodes to. -/
def obs {S : Type} [EngineDb S] (r : ResultCode × List TradeObs) (s : S) : Obs :=
  { code := r.1, trades := r.2, book := bookView (absBook (EngineDb.view s)) }

-- ============================================================================
-- cancelOrder preserves the invariants (the spec had no theorem for it)
-- ============================================================================

theorem pairwise_of_bidsSorted :
    ∀ {l : List PriceLevel}, bidsSortedDescB l = true →
      l.Pairwise (fun a b => b.price < a.price)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [bidsSortedDescB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_bidsSorted h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans (List.rel_of_pairwise_cons ih hx) h.1

theorem bidsSorted_of_pairwise' :
    ∀ {l : List PriceLevel}, l.Pairwise (fun a b => b.price < a.price) →
      bidsSortedDescB l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [bidsSortedDescB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self,
      bidsSorted_of_pairwise' (List.Pairwise.of_cons h)⟩

theorem pairwise_of_asksSorted :
    ∀ {l : List PriceLevel}, asksSortedAscB l = true →
      l.Pairwise (fun a b => a.price < b.price)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [asksSortedAscB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_asksSorted h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem asksSorted_of_pairwise' :
    ∀ {l : List PriceLevel}, l.Pairwise (fun a b => a.price < b.price) →
      asksSortedAscB l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [asksSortedAscB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self,
      asksSorted_of_pairwise' (List.Pairwise.of_cons h)⟩

/-- Each level `removeLevelOrder` keeps is an input level with some orders
    filtered out, never empty. -/
theorem mem_removeLevelOrder {L : List PriceLevel} {oid : OrderId} {l' : PriceLevel}
    (h : l' ∈ removeLevelOrder L oid) :
    ∃ l ∈ L, l'.price = l.price ∧ l'.orders = l.orders.filter (·.id != oid) ∧
      l'.orders ≠ [] := by
  unfold removeLevelOrder at h
  obtain ⟨l, hl, hf⟩ := List.mem_filterMap.mp h
  simp only at hf
  split at hf
  · cases hf
  · rename_i hne
    cases hf
    exact ⟨l, hl, rfl, rfl, by simpa using hne⟩

theorem removeLevelOrder_pairwise {R : Nat → Nat → Prop} {L : List PriceLevel}
    {oid : OrderId} (h : L.Pairwise (fun a b => R a.price b.price)) :
    (removeLevelOrder L oid).Pairwise (fun a b => R a.price b.price) := by
  unfold removeLevelOrder
  refine List.Pairwise.filterMap _ (fun a a' hr b hb b' hb' => ?_) h
  simp only at hb hb'
  split at hb
  · cases hb
  · split at hb'
    · cases hb'
    · cases hb; cases hb'; exact hr

/-- The head of a sorted side dominates every level on it. -/
theorem head_dominates {R : Nat → Nat → Prop}
    {x : PriceLevel} {xs : List PriceLevel}
    (h : (x :: xs).Pairwise (fun a b => R a.price b.price)) :
    ∀ y ∈ x :: xs, y = x ∨ R x.price y.price := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact Or.inl rfl
  · exact Or.inr (List.rel_of_pairwise_cons h hy)

theorem SideOk_removeLevelOrder {n : Timestamp} {L : List PriceLevel} {oid : OrderId}
    (h : SideOk n L) : SideOk n (removeLevelOrder L oid) := by
  intro l' hl'
  obtain ⟨l, hl, -, ho, hne⟩ := mem_removeLevelOrder hl'
  obtain ⟨-, hfifo, hrest⟩ := h l hl
  refine ⟨hne, ?_, fun o ho' => ?_⟩
  · rw [ho]; exact hfifo.filter _
  · rw [ho] at ho'; exact hrest o (List.mem_filter.mp ho').1

/-- Removing orders from the bid side keeps the book uncrossed: the new best
    bid is at or below the old one. -/
theorem uncrossed_bids {b : BookState} {oid : OrderId} (hu : BookUncrossed b)
    (hs : bidsSortedDescB b.bids = true) :
    BookUncrossed { b with bids := removeLevelOrder b.bids oid } := by
  unfold BookUncrossed bestBidPrice bestAskPrice at *
  cases hn : removeLevelOrder b.bids oid with
  | nil => simp
  | cons x' xs' =>
    obtain ⟨x, hx, hp, -, -⟩ := mem_removeLevelOrder (show x' ∈ removeLevelOrder b.bids oid by
      rw [hn]; exact List.mem_cons_self)
    cases hb : b.bids with
    | nil => rw [hb] at hx; cases hx
    | cons y ys =>
      rw [hb] at hx hs hu
      have hdom := head_dominates (R := fun p q => q < p)
        (pairwise_of_bidsSorted hs) x hx
      cases ha : b.asks.head? with
      | none => simp
      | some a =>
        simp only [List.head?_cons, Option.map_some, ha] at hu ⊢
        rcases hdom with rfl | hlt
        · rw [hp]; exact hu
        · rw [hp]; exact Nat.lt_trans hlt hu

theorem uncrossed_asks {b : BookState} {oid : OrderId} (hu : BookUncrossed b)
    (hs : asksSortedAscB b.asks = true) :
    BookUncrossed { b with asks := removeLevelOrder b.asks oid } := by
  unfold BookUncrossed bestBidPrice bestAskPrice at *
  cases hn : removeLevelOrder b.asks oid with
  | nil => cases b.bids.head? <;> simp
  | cons x' xs' =>
    obtain ⟨x, hx, hp, -, -⟩ := mem_removeLevelOrder (show x' ∈ removeLevelOrder b.asks oid by
      rw [hn]; exact List.mem_cons_self)
    cases hb : b.asks with
    | nil => rw [hb] at hx; cases hx
    | cons y ys =>
      rw [hb] at hx hs hu
      have hdom := head_dominates (R := fun p q => p < q)
        (pairwise_of_asksSorted hs) x hx
      cases hd : b.bids.head? with
      | none => simp
      | some d =>
        simp only [List.head?_cons, Option.map_some, hd] at hu ⊢
        rcases hdom with rfl | hlt
        · rw [hp]; exact hu
        · rw [hp]; exact Nat.lt_trans hu hlt

theorem cancelOrder_preserves_ProcessInv {b b' : BookState} {oid : OrderId}
    (hinv : ProcessInv b) (hc : cancelOrder b oid = some b') : ProcessInv b' := by
  obtain ⟨⟨hu, hbs, has⟩, ⟨hbok, haok⟩, hswf, hsnp⟩ := hinv
  unfold cancelOrder at hc
  split at hc
  · cases hc
  · rename_i side _ _
    cases side with
    | buy =>
      simp only [Option.some.injEq] at hc; subst hc
      exact ⟨⟨uncrossed_bids hu hbs,
          bidsSorted_of_pairwise' (removeLevelOrder_pairwise (R := fun p q => q < p) (pairwise_of_bidsSorted hbs)), has⟩,
        ⟨SideOk_removeLevelOrder hbok, haok⟩, hswf, hsnp⟩
    | sell =>
      simp only [Option.some.injEq] at hc; subst hc
      exact ⟨⟨uncrossed_asks hu has, hbs,
          asksSorted_of_pairwise' (removeLevelOrder_pairwise (R := fun p q => p < q) (pairwise_of_asksSorted has))⟩,
        ⟨hbok, SideOk_removeLevelOrder haok⟩, hswf, hsnp⟩

-- ============================================================================
-- Transfer lemmas
-- ============================================================================

/-- A step either accepts an order, cancels one, or rejects with the input
    book unchanged and no trade. -/
theorem processB_cases (cap : Nat) (b : BookState) (req : Req) :
    (processB cap b req).2 = { book := b, trades := [] } ∨
    (processB cap b req).1 = .accepted ∨ (processB cap b req).1 = .cancelled := by
  unfold processB
  cases req with
  | order r =>
    simp only
    repeat' split
    all_goals simp [rejectWith]
  | cancel id =>
    simp only
    split <;> simp [rejectWith]

/-- Every rejection returns the input book and no trade. -/
theorem processB_rejected {cap : Nat} {b : BookState} {req : Req}
    (h : (processB cap b req).1 ≠ .accepted ∧ (processB cap b req).1 ≠ .cancelled) :
    (processB cap b req).2 = { book := b, trades := [] } := by
  rcases processB_cases cap b req with h' | h' | h'
  · exact h'
  · exact absurd h' h.1
  · exact absurd h' h.2

/-- The loop invariant of the spec survives one `processB` step. -/
theorem processB_preserves_ProcessInv (cap : Nat) {b : BookState} (req : Req)
    (hinv : ProcessInv b) : ProcessInv (processB cap b req).2.book := by
  unfold processB
  cases req with
  | order r =>
    simp only
    split
    · exact hinv
    · split
      · exact hinv
      · rename_i o ho
        have hwf := toSpec_wellFormed ho
        split
        · exact hinv
        · split
          · exact hinv
          · split
            · exact hinv
            · split
              · exact hinv
              · exact ProcessInv_step { b with nextId := o.id } o hinv
                  (OrderProcOk_of_WellFormed hwf) (OrderRestOk_of_WellFormed hwf)
  | cancel id =>
    simp only
    split
    · exact hinv
    · rename_i b' hc
      exact cancelOrder_preserves_ProcessInv hinv hc

/-- §13 book invariants after a `processB` step. -/
theorem processB_BookInvariant (cap : Nat) {b : BookState} (req : Req)
    (hinv : ProcessInv b) : BookInvariant (processB cap b req).2.book :=
  BookInvariant_of_ProcessInv (processB_preserves_ProcessInv cap req hinv)

theorem processB_AllInv (cap : Nat) {b : BookState} (req : Req)
    (hinv : ProcessInv b) : AllInv (processB cap b req).2.book :=
  (processB_preserves_ProcessInv cap req hinv).1

/-- INV-11 and INV-12 for every trade `processB` emits, unconditionally. -/
theorem processB_trades_ok (cap : Nat) (b : BookState) (req : Req) :
    PostOnlyGuarantee (processB cap b req).2.trades ∧
    STPGuarantee (processB cap b req).2.trades := by
  unfold processB
  cases req with
  | order r =>
    simp only
    split
    · simp [rejectWith, PostOnlyGuarantee, STPGuarantee]
    · split
      · simp [rejectWith, PostOnlyGuarantee, STPGuarantee]
      · rename_i o _
        split
        · simp [rejectWith, PostOnlyGuarantee, STPGuarantee]
        · split
          · simp [rejectWith, PostOnlyGuarantee, STPGuarantee]
          · split
            · simp [rejectWith, PostOnlyGuarantee, STPGuarantee]
            · split
              · simp [rejectWith, PostOnlyGuarantee, STPGuarantee]
              · exact ⟨processWithId_PostOnlyGuarantee b o, processWithId_STPGuarantee b o⟩
  | cancel id =>
    simp only
    split
    · simp [rejectWith, PostOnlyGuarantee, STPGuarantee]
    · simp [rejectWith, PostOnlyGuarantee, STPGuarantee]

/-- Run a request sequence from the empty book. -/
def runB (cap : Nat) : BookState → List Req → BookState
  | b, [] => b
  | b, r :: rs => runB cap (processB cap b r).2.book rs

theorem runB_ProcessInv (cap : Nat) : ∀ (reqs : List Req) (b : BookState),
    ProcessInv b → ProcessInv (runB cap b reqs)
  | [], _, h => h
  | r :: rs, b, h => runB_ProcessInv cap rs _ (processB_preserves_ProcessInv cap r h)

/-- **Reachable states of `processB`.** Every book reached from the empty book
    by any sequence of requests satisfies the full §13 book invariant. -/
theorem runB_BookInvariant (cap : Nat) (reqs : List Req) :
    BookInvariant (runB cap BookState.empty reqs) :=
  BookInvariant_of_ProcessInv (runB_ProcessInv cap reqs _ ProcessInv_empty)

end ProcessB
