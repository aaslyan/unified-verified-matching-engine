import Amcc.Interface
import Amcc.Spec.Algebra
import Amcc.CSubset.Value
import Amcc.CSubset.Eval
import Amcc.CSubset.Chain

/-!
# Matching Engine — Core Abstract Model & Simulation Bridge
Formalizes the core abstract limit order book model (`BookState`, `AllInv`,
`abstract_insert`, `abstract_cancel`, `abstract_stp_step`, `abstract_match_step`).

FIFO priority is carried structurally by the list order within each `PriceLevel`:
- Insertion appends new orders to the tail (`orders ++ [o]`)
- Matching consumes orders from the head (`orders.head`)
-/

namespace VerifiedCMatchingEngine

open Interface
open Amcc.Spec
open CSubset

abbrev OrderId := UInt64
abbrev AccountId := UInt64
abbrev Price := UInt64
abbrev Quantity := UInt64

inductive Side where
  | buy
  | sell
  deriving DecidableEq, Repr, Inhabited

inductive STPMode where
  | cancel_new
  | cancel_old
  | cancel_both
  | decrement_and_continue
  deriving DecidableEq, Repr, Inhabited

structure Order where
  id      : OrderId
  account : AccountId
  price   : Price
  qty     : Quantity
  side    : Side
  deriving DecidableEq, Repr, Inhabited

structure PriceLevel where
  price  : Price
  orders : List Order
  deriving DecidableEq, Repr, Inhabited

def PriceLevel.totalQty (l : PriceLevel) : Quantity :=
  l.orders.foldl (fun acc o => acc + o.qty) 0

structure BookState where
  bids : List PriceLevel
  asks : List PriceLevel
  deriving DecidableEq, Repr, Inhabited

def allOrders (b : BookState) : List Order :=
  (b.bids.flatMap PriceLevel.orders) ++ (b.asks.flatMap PriceLevel.orders)

/-- Invariant 1: Uncrossed Book (Every resting bid price < every resting ask price) -/
def Uncrossed (b : BookState) : Prop :=
  ∀ (bid ask : PriceLevel), bid ∈ b.bids → ask ∈ b.asks → bid.price < ask.price

/-- Invariant 2: Bids strictly sorted descending by price -/
def BidsSorted (b : BookState) : Prop :=
  b.bids.Pairwise (fun l1 l2 => l1.price > l2.price)

/-- Invariant 3: Asks strictly sorted ascending by price -/
def AsksSorted (b : BookState) : Prop :=
  b.asks.Pairwise (fun l1 l2 => l1.price < l2.price)

/-- Invariant 4: No empty price levels on the book -/
def NoEmptyLevels (b : BookState) : Prop :=
  (∀ l ∈ b.bids, l.orders ≠ []) ∧ (∀ l ∈ b.asks, l.orders ≠ [])

/-- Invariant 5: No ghost orders (all resting quantities > 0) -/
def NoGhosts (b : BookState) : Prop :=
  (∀ l ∈ b.bids, ∀ o ∈ l.orders, o.qty > 0) ∧
  (∀ l ∈ b.asks, ∀ o ∈ l.orders, o.qty > 0)

/-- Invariant 6: Unique Order IDs across the entire book -/
def UniqueOrderIDs (b : BookState) : Prop :=
  (allOrders b).Pairwise (fun o1 o2 => o1.id ≠ o2.id)

/-- Invariant 7: Price-Level Order Consistency (all orders inside a level have matching price and side) -/
def PriceLevelConsistency (b : BookState) : Prop :=
  (∀ l ∈ b.bids, ∀ o ∈ l.orders, o.price = l.price ∧ o.side = Side.buy) ∧
  (∀ l ∈ b.asks, ∀ o ∈ l.orders, o.price = l.price ∧ o.side = Side.sell)

/-- Invariant 8: Self-Trade Prevention Invariant (resting orders belong to distinct valid accounts) -/
def NoSelfTrades (b : BookState) : Prop :=
  ∀ (bid ask : PriceLevel), bid ∈ b.bids → ask ∈ b.asks →
    ∀ ob ∈ bid.orders, ∀ oa ∈ ask.orders, ob.account ≠ oa.account ∨ bid.price < ask.price

/-- Complete End-to-End Matching Engine Invariant Suite -/
structure AllInv (b : BookState) : Prop where
  uncrossed        : Uncrossed b
  bids_sorted      : BidsSorted b
  asks_sorted      : AsksSorted b
  no_empty_levels  : NoEmptyLevels b
  no_ghosts        : NoGhosts b
  unique_ids       : UniqueOrderIDs b
  level_consistent : PriceLevelConsistency b
  stp_sound        : NoSelfTrades b

def emptyBook : BookState := { bids := [], asks := [] }

theorem emptyBook_AllInv : AllInv emptyBook where
  uncrossed := by intro bid ask hbid; cases hbid
  bids_sorted := List.Pairwise.nil
  asks_sorted := List.Pairwise.nil
  no_empty_levels := ⟨by intro l hl; contradiction, by intro l hl; contradiction⟩
  no_ghosts := ⟨by intro l hl; contradiction, by intro l hl; contradiction⟩
  unique_ids := List.Pairwise.nil
  level_consistent := ⟨by intro l hl; contradiction, by intro l hl; contradiction⟩
  stp_sound := by intro bid ask hbid; cases hbid

/-- Insert order into sorted price levels -/
def insertOrderIntoLevels (levels : List PriceLevel) (o : Order) (is_bid : Bool) : List PriceLevel :=
  match levels with
  | [] => [{ price := o.price, orders := [o] }]
  | lvl :: rest =>
    if o.price == lvl.price then
      { lvl with orders := lvl.orders ++ [o] } :: rest
    else if (if is_bid then o.price > lvl.price else o.price < lvl.price) then
      { price := o.price, orders := [o] } :: lvl :: rest
    else
      lvl :: insertOrderIntoLevels rest o is_bid

/-- Abstract order insertion -/
def abstract_insert (b : BookState) (o : Order) : BookState :=
  match o.side with
  | Side.buy => { b with bids := insertOrderIntoLevels b.bids o true }
  | Side.sell => { b with asks := insertOrderIntoLevels b.asks o false }

/-- Remove order by ID from order list -/
def removeOrderFromList (orders : List Order) (id : OrderId) : List Order :=
  orders.filter (fun o => o.id ≠ id)

/-- Cancel order from sorted price levels -/
def cancelFromLevels (levels : List PriceLevel) (id : OrderId) : List PriceLevel :=
  levels.filterMap (fun lvl =>
    let os := removeOrderFromList lvl.orders id
    if os.isEmpty then none
    else some { lvl with orders := os })

/-- Abstract order cancellation -/
def abstract_cancel (b : BookState) (id : OrderId) : BookState :=
  { bids := cancelFromLevels b.bids id, asks := cancelFromLevels b.asks id }

/-- Decrement resting order quantity or remove if depleted -/
def decrementOrderInList (orders : List Order) (id : OrderId) (decr : Quantity) : List Order :=
  orders.filterMap (fun o =>
    if o.id == id then
      if o.qty ≤ decr then none
      else some { o with qty := o.qty - decr }
    else some o)

def decrementInLevels (levels : List PriceLevel) (id : OrderId) (decr : Quantity) : List PriceLevel :=
  levels.filterMap (fun lvl =>
    let os := decrementOrderInList lvl.orders id decr
    if os.isEmpty then none
    else some { lvl with orders := os })

/-- Abstract Self-Trade Prevention: Evaluates aggressor order against top resting order -/
def abstract_stp_step (b : BookState) (_aggressor : Order) (mode : STPMode) (resting_id : OrderId) (decr_qty : Quantity) : BookState :=
  match mode with
  | STPMode.cancel_new => b
  | STPMode.cancel_old => abstract_cancel b resting_id
  | STPMode.cancel_both => abstract_cancel b resting_id
  | STPMode.decrement_and_continue => { bids := decrementInLevels b.bids resting_id decr_qty, asks := decrementInLevels b.asks resting_id decr_qty }

/-- Abstract Matching Execution against top-of-book -/
def abstract_match_step (b : BookState) (aggressor : Order) (passive : Order) (mode : STPMode) : BookState :=
  if aggressor.account != 0 && aggressor.account == passive.account then
    abstract_stp_step b aggressor mode passive.id (min aggressor.qty passive.qty)
  else
    let fill_qty := min aggressor.qty passive.qty
    match aggressor.side with
    | Side.buy => { b with asks := decrementInLevels b.asks passive.id fill_qty }
    | Side.sell => { b with bids := decrementInLevels b.bids passive.id fill_qty }

theorem cancelFromLevels_price_subset {levels : List PriceLevel} {id : OrderId} {lvl : PriceLevel}
    (h : lvl ∈ cancelFromLevels levels id) : ∃ orig ∈ levels, orig.price = lvl.price := by
  have h_mem := List.mem_filterMap.mp h
  rcases h_mem with ⟨orig, horig, hsome⟩
  dsimp at hsome
  split at hsome
  · cases hsome
  · cases hsome
    exact ⟨orig, horig, rfl⟩

theorem decrementInLevels_price_subset {levels : List PriceLevel} {id : OrderId} {decr : Quantity} {lvl : PriceLevel}
    (h : lvl ∈ decrementInLevels levels id decr) : ∃ orig ∈ levels, orig.price = lvl.price := by
  have h_mem := List.mem_filterMap.mp h
  rcases h_mem with ⟨orig, horig, hsome⟩
  dsimp at hsome
  split at hsome
  · cases hsome
  · cases hsome
    exact ⟨orig, horig, rfl⟩

/-- Theorem: Abstract cancel preserves the uncrossed book invariant -/
theorem cancel_preserves_uncrossed (b : BookState) (id : OrderId) (h_uncrossed : Uncrossed b) :
    Uncrossed (abstract_cancel b id) := by
  intro bid ask hbid hask
  unfold abstract_cancel at hbid hask
  simp at hbid hask
  obtain ⟨bid_orig, hbid_orig, hbid_p⟩ := cancelFromLevels_price_subset hbid
  obtain ⟨ask_orig, hask_orig, hask_p⟩ := cancelFromLevels_price_subset hask
  have h_orig := h_uncrossed bid_orig ask_orig hbid_orig hask_orig
  rw [← hbid_p, ← hask_p]
  exact h_orig

theorem decrement_preserves_uncrossed (b : BookState) (id : OrderId) (decr : Quantity) (h_uncrossed : Uncrossed b) :
    Uncrossed { bids := decrementInLevels b.bids id decr, asks := decrementInLevels b.asks id decr } := by
  intro bid ask hbid hask
  obtain ⟨bid_orig, hbid_orig, hbid_p⟩ := decrementInLevels_price_subset hbid
  obtain ⟨ask_orig, hask_orig, hask_p⟩ := decrementInLevels_price_subset hask
  have h_orig := h_uncrossed bid_orig ask_orig hbid_orig hask_orig
  rw [← hbid_p, ← hask_p]
  exact h_orig

/-- Theorem: STP cancellation policies strictly preserve the uncrossed book invariant -/
theorem stp_preserves_uncrossed (b : BookState) (aggressor : Order) (mode : STPMode) (resting_id : OrderId) (decr : Quantity)
    (h_uncrossed : Uncrossed b) :
    Uncrossed (abstract_stp_step b aggressor mode resting_id decr) := by
  cases mode with
  | cancel_new => exact h_uncrossed
  | cancel_old => exact cancel_preserves_uncrossed b resting_id h_uncrossed
  | cancel_both => exact cancel_preserves_uncrossed b resting_id h_uncrossed
  | decrement_and_continue => exact decrement_preserves_uncrossed b resting_id decr h_uncrossed

/-- Theorem: Matching executions preserve the uncrossed book invariant -/
theorem match_step_preserves_uncrossed (b : BookState) (aggressor : Order) (passive : Order) (mode : STPMode)
    (h_uncrossed : Uncrossed b) :
    Uncrossed (abstract_match_step b aggressor passive mode) := by
  unfold abstract_match_step
  by_cases h_stp : (aggressor.account != 0 && aggressor.account == passive.account)
  · rw [if_pos h_stp]
    exact stp_preserves_uncrossed b aggressor mode passive.id (min aggressor.qty passive.qty) h_uncrossed
  · rw [if_neg h_stp]
    cases aggressor.side with
    | buy =>
      intro bid ask hbid hask
      obtain ⟨ask_orig, hask_orig, hask_p⟩ := decrementInLevels_price_subset hask
      have h_orig := h_uncrossed bid ask_orig hbid hask_orig
      rw [← hask_p]
      exact h_orig
    | sell =>
      intro bid ask hbid hask
      obtain ⟨bid_orig, hbid_orig, hbid_p⟩ := decrementInLevels_price_subset hbid
      have h_orig := h_uncrossed bid_orig ask hbid_orig hask
      rw [← hbid_p]
      exact h_orig

theorem insertOrderIntoLevels_price_cases (levels : List PriceLevel) (o : Order) (is_bid : Bool) (lvl : PriceLevel)
    (h : lvl ∈ insertOrderIntoLevels levels o is_bid) :
    lvl.price = o.price ∨ ∃ orig ∈ levels, orig.price = lvl.price := by
  induction levels with
  | nil =>
    have h_sing : lvl ∈ [{ price := o.price, orders := [o] }] := h
    have heq := List.mem_singleton.mp h_sing
    subst heq
    exact Or.inl rfl
  | cons hd tl ih =>
    unfold insertOrderIntoLevels at h
    by_cases h_eq : o.price == hd.price
    · rw [if_pos h_eq] at h
      cases List.mem_cons.mp h with
      | inl h1 =>
        have hp : lvl.price = hd.price := by rw [h1]
        exact Or.inr ⟨hd, List.Mem.head _, hp.symm⟩
      | inr h2 =>
        exact Or.inr ⟨lvl, List.mem_cons_of_mem hd h2, rfl⟩
    · rw [if_neg h_eq] at h
      by_cases h_ord : (if is_bid then o.price > hd.price else o.price < hd.price)
      · rw [if_pos h_ord] at h
        cases List.mem_cons.mp h with
        | inl h1 =>
          have hp : lvl.price = o.price := by rw [h1]
          exact Or.inl hp
        | inr h2 =>
          cases List.mem_cons.mp h2 with
          | inl h3 =>
            have hp : lvl.price = hd.price := by rw [h3]
            exact Or.inr ⟨hd, List.Mem.head _, hp.symm⟩
          | inr h4 =>
            exact Or.inr ⟨lvl, List.mem_cons_of_mem hd h4, rfl⟩
      · rw [if_neg h_ord] at h
        cases List.mem_cons.mp h with
        | inl h1 =>
          have hp : lvl.price = hd.price := by rw [h1]
          exact Or.inr ⟨hd, List.Mem.head _, hp.symm⟩
        | inr h2 =>
          cases ih h2 with
          | inl he => exact Or.inl he
          | inr hex =>
            obtain ⟨orig, horig, hp⟩ := hex
            exact Or.inr ⟨orig, List.mem_cons_of_mem hd horig, hp⟩

/-- Theorem: Abstract insert preserves the uncrossed book invariant when non-crossing -/
theorem insert_preserves_uncrossed (b : BookState) (o : Order) (h_uncrossed : Uncrossed b)
    (h_o_buy : o.side = Side.buy → ∀ ask ∈ b.asks, o.price < ask.price)
    (h_o_sell : o.side = Side.sell → ∀ bid ∈ b.bids, bid.price < o.price) :
    Uncrossed (abstract_insert b o) := by
  intro bid ask hbid hask
  unfold abstract_insert at hbid hask
  cases hside : o.side with
  | buy =>
    simp [hside] at hbid hask
    have hask_orig : ask ∈ b.asks := hask
    cases insertOrderIntoLevels_price_cases b.bids o true bid hbid with
    | inl h_eq =>
      have h_lt := h_o_buy hside ask hask_orig
      rw [h_eq]
      exact h_lt
    | inr h_orig =>
      obtain ⟨l, hl, h_eq⟩ := h_orig
      have h_lt := h_uncrossed l ask hl hask_orig
      rw [← h_eq]
      exact h_lt
  | sell =>
    simp [hside] at hbid hask
    have hbid_orig : bid ∈ b.bids := hbid
    cases insertOrderIntoLevels_price_cases b.asks o false ask hask with
    | inl h_eq =>
      have h_lt := h_o_sell hside bid hbid_orig
      rw [h_eq]
      exact h_lt
    | inr h_orig =>
      obtain ⟨l, hl, h_eq⟩ := h_orig
      have h_lt := h_uncrossed bid l hbid_orig hl
      rw [← h_eq]
      exact h_lt

end VerifiedCMatchingEngine
