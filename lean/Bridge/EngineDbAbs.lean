import MatchingEngine
import Bridge.EngineDbApiLaws

/-!
# Abstraction map from the EngineDb store to the spec book

Prompt 3 of `docs/c-verification-plan.md`. This file connects the abstract
EngineDb store (`EngineDbApi.Db`) that the C client manipulates with the
spec's `BookState`, and the C request (`OrderRequest`) with the spec's `Order`.

1. `CRequest`, its decoders, and `CRequest.toSpec : CRequest → Option Order`,
   following the mapping table of `docs/c-vs-spec-divergences.md` §0 with the
   C STP rule (D2/D3). `processWithId` is the spec step with the caller's id
   (decision D1); `processWithId_eq_process` shows it is `process` whenever
   `nextId` already equals the id.
2. `absBook : Db → BookState`.
3. `ClientInv : Db → Prop`, the client-side representation invariant.
4. `ClientInv_empty`, `absBook_AllInv`, `absBook_BookInvariant`
   (and `absBook_ProcessInv`, the full precondition bundle of `process`).

## Fields the C store does not have

The C `struct Order` keeps `id, account_id, side, stp_mode, price, qty,
remaining_qty`; `struct PriceLevel` keeps `price, total_qty`. Every other spec
field is either determined by what C can hold, or synthesized and then
forgotten by the projection `bookView`:

| spec field | resolution in `absBook` |
|---|---|
| `Order.orderType` | `.limit`: C rests only LIMIT and POST_ONLY, both map to `.limit` (exact) |
| `Order.tif` | `.gtc`: both resting types map to GTC (exact) |
| `Order.stopPrice`, `displayQty`, `minQty` | `none`: C has no stops, icebergs or minimum quantity; `insertOrder` clears `minQty` anyway (exact) |
| `Order.visibleQty` | `remaining`: without icebergs the spec keeps `visibleQty = remainingQty` (exact) |
| `Order.postOnly` | synthesized `false`; forgotten by `bookView`. C does not remember whether a resting order was POST_ONLY, and the spec never reads the flag of a resting order |
| `Order.status` | synthesized `new_` if `remaining = qty`, else `partiallyFilled`; forgotten by `bookView`. The spec's value is not a function of C's state: an STP decrement lowers `remainingQty` without changing status |
| `Order.timestamp` | synthesized: the order's position in its level's queue; forgotten by `bookView`. Strictly increasing along the queue, so INV-7 holds; no spec branch reachable from C requests reads a resting timestamp (only iceberg reload and stop sorting do) |
| `BookState.stops` | `[]` (exact: C has no stop orders); kept by `bookView` |
| `BookState.lastTradePrice` | synthesized `none`; forgotten by `bookView` (only read by stop triggering) |
| `BookState.nextId` | synthesized `1`; forgotten by `bookView`. `processWithId` overwrites it with the request id (D1) |
| `BookState.clock` | synthesized `1 + number of resting orders`, strictly above every synthesized timestamp (so `BookOk` holds); forgotten by `bookView` |
| `PriceLevel.totalQty` (C only) | no spec counterpart; `ClientInv.total_qty` pins it to the sum of remaining quantities |
| `Order.account` / `stp_mode` (C) | `stpGroup := stpGroupOf account`, `stpPolicy := stpPolicyOf account stp_mode` |
-/

namespace EngineDbAbs

open EngineDbApi

-- ============================================================================
-- 1. The C request (`OrderRequest` in c/include/matching_engine.h)
-- ============================================================================

/-- `OrderType`: `TYPE_LIMIT = 0`, `TYPE_MARKET = 1`, `TYPE_IOC = 2`,
    `TYPE_POST_ONLY = 3`. -/
inductive COrderType where
  | limit
  | market
  | ioc
  | postOnly
  deriving DecidableEq, Repr

/-- `StpMode`: `STP_NONE = 0` .. `STP_DECREMENT_AND_CONTINUE = 4`. -/
inductive CStpMode where
  | none
  | cancelNew
  | cancelOld
  | cancelBoth
  | decrement
  deriving DecidableEq, Repr

/-- `struct OrderRequest`, field for field. The enums are raw `uint8_t`s, as
    in C; out-of-range values are rejected (D11). -/
structure CRequest where
  id        : UInt64
  account   : UInt64
  side      : UInt8
  orderType : UInt8
  stpMode   : UInt8
  price     : UInt64
  qty       : UInt64
  deriving DecidableEq, Repr

def decodeSide (s : UInt8) : Option Side :=
  match s.toNat with
  | 0 => some .buy
  | 1 => some .sell
  | _ => none

def decodeOrderType (t : UInt8) : Option COrderType :=
  match t.toNat with
  | 0 => some .limit
  | 1 => some .market
  | 2 => some .ioc
  | 3 => some .postOnly
  | _ => none

def decodeStpMode (m : UInt8) : Option CStpMode :=
  match m.toNat with
  | 0 => some .none
  | 1 => some .cancelNew
  | 2 => some .cancelOld
  | 3 => some .cancelBoth
  | 4 => some .decrement
  | _ => none

/-- The spec policy of a C mode; `none` for `STP_NONE` (the order opts out). -/
def CStpMode.policy : CStpMode → Option STPPolicy
  | .none       => Option.none
  | .cancelNew  => some .cancelNewest
  | .cancelOld  => some .cancelOldest
  | .cancelBoth => some .cancelBoth
  | .decrement  => some .decrement

/-- The STP group of an account: `none` for account 0, which never conflicts. -/
def stpGroupOf (account : UInt64) : Option StpGroup :=
  if account = 0 then none else some account.toNat

/-- The STP policy of an (account, mode) pair. Account 0 gets `none` even
    when the mode is not NONE: C never detects a conflict for account 0
    (`req->account_id != 0` in the trigger), and the spec never detects one
    for an order without a group either, so dropping the policy there changes
    no behaviour, and it keeps WF-16 (`stpPolicy.isSome → stpGroup.isSome`). -/
def stpPolicyOf (account : UInt64) (mode : UInt8) : Option STPPolicy :=
  if account = 0 then none else (decodeStpMode mode).bind CStpMode.policy

def COrderType.specType : COrderType → OrderType
  | .market => .market
  | _       => .limit

def COrderType.tif : COrderType → TimeInForce
  | .market | .ioc => .ioc
  | _              => .gtc

def COrderType.isPostOnly : COrderType → Bool
  | .postOnly => true
  | _         => false

/-- MARKET carries no price (D5); every other type carries the C price. -/
def COrderType.specPrice (ot : COrderType) (p : UInt64) : Option Price :=
  match ot with
  | .market => none
  | _       => some p.toNat

/-- The spec order of a decoded request. The `id` is the C id (D1); the
    `timestamp` is a placeholder that `process` overwrites with the clock. -/
def CRequest.mkOrder (r : CRequest) (s : Side) (ot : COrderType) : Order :=
  { id := r.id.toNat, side := s, orderType := ot.specType, tif := ot.tif,
    price := ot.specPrice r.price, stopPrice := none,
    qty := r.qty.toNat, remainingQty := r.qty.toNat,
    minQty := none, displayQty := none, visibleQty := r.qty.toNat,
    postOnly := ot.isPostOnly, status := .new_, timestamp := 0,
    stpGroup := stpGroupOf r.account, stpPolicy := stpPolicyOf r.account r.stpMode }

/-- The request-only rejections at the top of `MatchingEngine_ProcessOrder`
    (matching_engine.c:20-22): zero quantity, out-of-range enums (D11), and
    price 0 on a priced type (D4). -/
def CRequest.staticReject (r : CRequest) : Bool :=
  r.qty == 0 || r.side > 1 || r.orderType > 3 || r.stpMode > 4 ||
    (r.orderType != 1 && r.price == 0)

/-- Map a C request to the spec order it stands for; `none` exactly when C
    rejects it before looking at the book (`toSpec_none_iff`). -/
def CRequest.toSpec (r : CRequest) : Option Order :=
  match decodeSide r.side, decodeOrderType r.orderType, decodeStpMode r.stpMode with
  | some s, some ot, some _ =>
    if r.qty = 0 then none
    else if ot ≠ .market ∧ r.price = 0 then none
    else some (r.mkOrder s ot)
  | _, _, _ => none

private theorem decodeSide_isSome (s : UInt8) : (decodeSide s).isSome ↔ s.toNat ≤ 1 := by
  unfold decodeSide; split <;> simp_all <;> omega

private theorem decodeOrderType_isSome (t : UInt8) :
    (decodeOrderType t).isSome ↔ t.toNat ≤ 3 := by
  unfold decodeOrderType; split <;> simp_all <;> omega

private theorem decodeStpMode_isSome (m : UInt8) :
    (decodeStpMode m).isSome ↔ m.toNat ≤ 4 := by
  unfold decodeStpMode; split <;> simp_all <;> omega

private theorem decodeOrderType_market {t : UInt8} {ot : COrderType}
    (h : decodeOrderType t = some ot) : ot = .market ↔ t = 1 := by
  have e : t = 1 ↔ t.toNat = 1 := by
    rw [← UInt8.toNat_inj]; rfl
  rw [e]
  unfold decodeOrderType at h
  split at h <;> simp_all <;> (try subst h) <;> simp_all

/-- `toSpec` rejects exactly the requests C rejects statically. -/
theorem toSpec_none_iff (r : CRequest) : r.toSpec = none ↔ r.staticReject = true := by
  have hs := decodeSide_isSome r.side
  have ht := decodeOrderType_isSome r.orderType
  have hm := decodeStpMode_isSome r.stpMode
  have e1 : r.side > 1 ↔ 1 < r.side.toNat := UInt8.lt_iff_toNat_lt
  have e3 : r.orderType > 3 ↔ 3 < r.orderType.toNat := UInt8.lt_iff_toNat_lt
  have e4 : r.stpMode > 4 ↔ 4 < r.stpMode.toNat := UInt8.lt_iff_toNat_lt
  unfold CRequest.toSpec CRequest.staticReject
  split
  · rename_i s ot md hs' ht' hm'
    have hmk := decodeOrderType_market ht'
    rw [hs'] at hs; rw [ht'] at ht; rw [hm'] at hm
    simp at hs ht hm
    by_cases hq : r.qty = 0
    · simp [hq]
    · by_cases hp : ot ≠ .market ∧ r.price = 0
      · have : r.orderType ≠ 1 := fun h => hp.1 (hmk.mpr h)
        simp [hq, hp, this]
      · have : ¬ (r.orderType ≠ 1 ∧ r.price = 0) := by
          intro ⟨h1, h2⟩; exact hp ⟨fun h => h1 (hmk.mp h), h2⟩
        simp only [hq, hp, if_false, reduceCtorEq, false_iff]
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true,
          bne_iff_ne, ne_eq, e1, e3, e4]
        intro hc
        rcases hc with ((((h | h) | h) | h) | h)
        · exact hq h
        · omega
        · omega
        · omega
        · exact this h
  · rename_i hnot
    simp only [true_iff]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true,
      bne_iff_ne, ne_eq]
    cases h1 : decodeSide r.side <;> cases h2 : decodeOrderType r.orderType <;>
      cases h3 : decodeStpMode r.stpMode <;> simp_all <;> omega

/-- Every request C accepts statically maps to a well-formed spec order
    (under the relaxed WF-16). -/
theorem toSpec_wellFormed {r : CRequest} {o : Order} (h : r.toSpec = some o) :
    o.WellFormed := by
  unfold CRequest.toSpec at h
  split at h
  · rename_i s ot md _ _ _
    by_cases hq : r.qty = 0
    · simp [hq] at h
    · by_cases hp : ot ≠ .market ∧ r.price = 0
      · simp [hq, hp] at h
      · simp only [hq, hp, if_false, Option.some.injEq] at h
        subst h
        have hq' : 0 < r.qty.toNat :=
          Nat.pos_of_ne_zero (fun h0 => hq (UInt64.toNat_inj.mp (by simpa using h0)))
        have hp' : ot ≠ .market → 0 < r.price.toNat := fun hm =>
          Nat.pos_of_ne_zero (fun h0 => hp ⟨hm, UInt64.toNat_inj.mp (by simpa using h0)⟩)
        have hstp : (stpPolicyOf r.account r.stpMode).isSome →
            (stpGroupOf r.account).isSome := by
          unfold stpPolicyOf stpGroupOf
          by_cases ha : r.account = 0 <;> simp [ha]
        cases ot <;>
          simp_all [Order.WellFormed, CRequest.mkOrder, COrderType.specType,
            COrderType.tif, COrderType.isPostOnly, COrderType.specPrice]
  · simp at h

-- ============================================================================
-- 1b. Order ids (decision D1)
-- ============================================================================

/-- The spec step with the caller's order id. `process` names the new order
    `b.nextId`; under D1 (the caller never reuses an id) the C id is used as
    the spec id directly, so the spec step is `process` run on the book whose
    `nextId` is the request's id. Nothing else in `process` reads `nextId`. -/
def processWithId (b : BookState) (o : Order) : ProcessResult :=
  process { b with nextId := o.id } o

/-- `processWithId` is `process` whenever the spec's id counter already
    equals the request id (e.g. a caller issuing ids 1, 2, 3, ...). -/
theorem processWithId_eq_process (b : BookState) (o : Order) (h : b.nextId = o.id) :
    processWithId b o = process b o := by
  unfold processWithId
  rw [← h]

/-- The order `processWithId` hands to `processOrder` carries the caller's id. -/
theorem processWithId_order_id (b : BookState) (o : Order) :
    ({ o with id := ({ b with nextId := o.id } : BookState).nextId,
               timestamp := ({ b with nextId := o.id } : BookState).clock } : Order).id
      = o.id := rfl

/-- The invariant theorems of `process` carry over to `processWithId`: the
    changed `nextId` is read by none of their hypotheses. -/
theorem processWithId_preserves_BookInvariant (b : BookState) (o : Order)
    (hall : AllInv b) (hpok : OrderProcOk o) (hsnp : StopsNoPostOnly b)
    (hb : BookOk b) (hstops : StopsWF b) (hok : OrderRestOk o) :
    BookInvariant (processWithId b o).book :=
  process_preserves_BookInvariant { b with nextId := o.id } o hall hpok hsnp hb hstops hok

theorem processWithId_STPGuarantee (b : BookState) (o : Order) :
    STPGuarantee (processWithId b o).trades :=
  process_STPGuarantee _ _

theorem processWithId_PostOnlyGuarantee (b : BookState) (o : Order) :
    PostOnlyGuarantee (processWithId b o).trades :=
  process_PostOnlyGuarantee _ _

-- ============================================================================
-- 2. The abstraction map
-- ============================================================================

def sideOfTree : Tree → Side
  | .bids => .buy
  | .asks => .sell

/-- The C `side` byte of the orders in a tree. -/
def sideCode : Tree → UInt8
  | .bids => 0
  | .asks => 1

/-- Placeholder row for a dead handle; never reached under `ClientInv`. -/
def OrderRow.dflt : OrderRow :=
  { id := 0, account := 0, side := 0, stpMode := 0, price := 0, qty := 0, remaining := 0 }

/-- The spec order of a resting C row at queue position `pos`. See the table
    in the module header for every field. -/
def restingOrder (t : Tree) (r : OrderRow) (pos : Nat) : Order :=
  { id := r.id.toNat, side := sideOfTree t, orderType := .limit, tif := .gtc,
    price := some r.price.toNat, stopPrice := none,
    qty := r.qty.toNat, remainingQty := r.remaining.toNat,
    minQty := none, displayQty := none, visibleQty := r.remaining.toNat,
    postOnly := false,
    status := if r.remaining = r.qty then .new_ else .partiallyFilled,
    timestamp := pos,
    stpGroup := stpGroupOf r.account, stpPolicy := stpPolicyOf r.account r.stpMode }

/-- A level's queue as spec orders, positions counted from `i`. -/
def absQueue (db : Db) (t : Tree) : Nat → List OrderH → List Order
  | _, [] => []
  | i, h :: hs => restingOrder t ((db.orders h).getD OrderRow.dflt) i :: absQueue db t (i + 1) hs

def absLevel (db : Db) (t : Tree) (l : LevelH) : PriceLevel :=
  { price := (db.levelPrice l).toNat, orders := absQueue db t 0 (db.queue l) }

/-- Strict priority of prices in a tree: higher bids, lower asks first. -/
def prioB : Tree → Nat → Nat → Bool
  | .bids, p, q => decide (q < p)
  | .asks, p, q => decide (p < q)

/-- Insert a level before the first level it has priority over. -/
def insLevel (t : Tree) (x : PriceLevel) : List PriceLevel → List PriceLevel
  | [] => [x]
  | y :: ys => if prioB t x.price y.price then x :: y :: ys else y :: insLevel t x ys

/-- Insertion sort by tree priority. -/
def sortLevels (t : Tree) : List PriceLevel → List PriceLevel
  | [] => []
  | x :: xs => insLevel t x (sortLevels t xs)

/-- One side of the spec book: the tree's levels, best first. -/
def absSide (db : Db) (t : Tree) : List PriceLevel :=
  sortLevels t ((db.tree t).map (absLevel db t))

/-- Number of orders resting in the two trees. -/
def restingCount (db : Db) : Nat :=
  ((db.tree .bids ++ db.tree .asks).map fun l => (db.queue l).length).sum

/-- The abstraction map. -/
def absBook (db : Db) : BookState :=
  { bids := absSide db .bids, asks := absSide db .asks, stops := [],
    lastTradePrice := none, nextId := 1, clock := restingCount db + 1 }

-- ----------------------------------------------------------------------------
-- Projection onto the fields C has
-- ----------------------------------------------------------------------------

/-- An order without the fields the C store does not keep (`postOnly`,
    `status`, `timestamp`). -/
structure OrderView where
  id           : OrderId
  side         : Side
  orderType    : OrderType
  tif          : TimeInForce
  price        : Option Price
  stopPrice    : Option Price
  qty          : Quantity
  remainingQty : Quantity
  minQty       : Option Quantity
  displayQty   : Option Quantity
  visibleQty   : Quantity
  stpGroup     : Option StpGroup
  stpPolicy    : Option STPPolicy
  deriving DecidableEq, Repr

def orderView (o : Order) : OrderView :=
  { id := o.id, side := o.side, orderType := o.orderType, tif := o.tif,
    price := o.price, stopPrice := o.stopPrice, qty := o.qty,
    remainingQty := o.remainingQty, minQty := o.minQty, displayQty := o.displayQty,
    visibleQty := o.visibleQty, stpGroup := o.stpGroup, stpPolicy := o.stpPolicy }

structure LevelView where
  price  : Price
  orders : List OrderView
  deriving DecidableEq, Repr

def levelView (l : PriceLevel) : LevelView :=
  { price := l.price, orders := l.orders.map orderView }

/-- A book without `lastTradePrice`, `nextId` and `clock`. `stops` is kept,
    so a spec book with the same view as `absBook db` has no stops. -/
structure BookView where
  bids  : List LevelView
  asks  : List LevelView
  stops : List OrderView
  deriving DecidableEq, Repr

def bookView (b : BookState) : BookView :=
  { bids := b.bids.map levelView, asks := b.asks.map levelView,
    stops := b.stops.map orderView }

/-- The row C writes when a request rests with `rem` left
    (matching_engine.c:119-126). -/
def CRequest.restRow (r : CRequest) (rem : UInt64) : OrderRow :=
  { id := r.id, account := r.account, side := r.side, stpMode := r.stpMode,
    price := r.price, qty := r.qty, remaining := rem }

/-- Resting a request: the order C builds from a LIMIT or POST_ONLY request
    that rests with `rem` left (matching_engine.c:119-126) is, up to the
    projection, the order the spec's `insertOrder` rests. -/
theorem restingOrder_matches_request (r : CRequest) (s : Side) (ot : COrderType)
    (t : Tree) (hst : sideOfTree t = s) (hot : ot = .limit ∨ ot = .postOnly)
    (rem : UInt64) (pos : Nat) :
    orderView (restingOrder t (r.restRow rem) pos)
      = orderView { r.mkOrder s ot with
          remainingQty := rem.toNat, visibleQty := rem.toNat, minQty := none } := by
  subst hst
  rcases hot with h | h <;> subst h <;> rfl

-- ============================================================================
-- 3. The client invariant
-- ============================================================================

/-- The representation invariant the C client maintains on top of `Db.WF`.
    That an order sits in at most one queue (its level is its only owner) is
    `Db.WF.queue_unique`, and distinct hashed ids are `Db.WF.hash_ids`. -/
structure ClientInv (db : Db) : Prop where
  /-- INV-1: no empty level in a tree. -/
  level_nonempty : ∀ t, ∀ l ∈ db.tree t, db.queue l ≠ []
  /-- Only levels in a tree hold orders. -/
  queue_in_tree  : ∀ l h, h ∈ db.queue l → l ∈ db.tree .bids ∨ l ∈ db.tree .asks
  /-- An order is hashed exactly when it is queued. -/
  hash_iff_queued : ∀ h, h ∈ db.hash ↔ db.queued h
  /-- Each queued order is live, matches its level's price and its tree's side,
      has positive remaining quantity not above its original quantity, and a
      valid STP mode. -/
  order_ok       : ∀ t, ∀ l ∈ db.tree t, ∀ h ∈ db.queue l, ∃ r,
                     db.orders h = some r ∧ r.side = sideCode t ∧
                     r.price = db.levelPrice l ∧ 0 < r.remaining ∧
                     r.remaining ≤ r.qty ∧ r.stpMode ≤ 4
  /-- `total_qty` is the sum of the remaining quantities (without overflow, D8). -/
  total_qty      : ∀ t, ∀ l ∈ db.tree t, ∃ lr, db.levels l = some lr ∧
                     lr.totalQty.toNat = ((db.queue l).map fun h => (db.orderRemaining h).toNat).sum
  /-- Resting prices are positive (C rejects price 0 on priced types, D4). -/
  price_pos      : ∀ t, ∀ l ∈ db.tree t, 0 < db.levelPrice l
  /-- INV-4 on the store: every bid price is below every ask price. -/
  uncrossed      : ∀ lb ∈ db.tree .bids, ∀ la ∈ db.tree .asks,
                     db.levelPrice lb < db.levelPrice la

-- ============================================================================
-- 4. Proofs
-- ============================================================================

theorem ClientInv_empty : ClientInv Db.empty where
  level_nonempty := by intro t l hl; cases hl
  queue_in_tree := by intro l h hh; cases hh
  hash_iff_queued := by intro h; simp [Db.queued, Db.empty]
  order_ok := by intro t l hl; cases hl
  total_qty := by intro t l hl; cases hl
  price_pos := by intro t l hl; cases hl
  uncrossed := by intro lb hl; cases hl

theorem absBook_empty : absBook Db.empty = BookState.empty := rfl

theorem absBook_empty_view : bookView (absBook Db.empty) = bookView BookState.empty := rfl

-- ----------------------------------------------------------------------------
-- Sorting
-- ----------------------------------------------------------------------------

private theorem prioB_trans {t : Tree} {a b c : Nat}
    (h1 : prioB t a b = true) (h2 : prioB t b c = true) : prioB t a c = true := by
  cases t <;> simp [prioB] at * <;> omega

private theorem prioB_total {t : Tree} {a b : Nat} (hne : a ≠ b)
    (h : ¬ prioB t a b = true) : prioB t b a = true := by
  cases t <;> simp [prioB] at * <;> omega

theorem mem_insLevel {t : Tree} {x y : PriceLevel} {ys : List PriceLevel} :
    y ∈ insLevel t x ys ↔ y = x ∨ y ∈ ys := by
  induction ys with
  | nil => simp [insLevel]
  | cons z zs ih =>
    unfold insLevel
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

theorem mem_sortLevels {t : Tree} {y : PriceLevel} {xs : List PriceLevel} :
    y ∈ sortLevels t xs ↔ y ∈ xs := by
  induction xs with
  | nil => simp [sortLevels]
  | cons x xs ih => simp [sortLevels, mem_insLevel, ih]

private abbrev LvPrio (t : Tree) (a b : PriceLevel) : Prop := prioB t a.price b.price = true

private theorem insLevel_pairwise {t : Tree} {x : PriceLevel} {ys : List PriceLevel}
    (hs : ys.Pairwise (LvPrio t)) (hx : ∀ y ∈ ys, x.price ≠ y.price) :
    (insLevel t x ys).Pairwise (LvPrio t) := by
  induction ys with
  | nil => simp [insLevel]
  | cons y ys ih =>
    rw [List.pairwise_cons] at hs
    unfold insLevel
    split
    · rename_i hxy
      refine List.Pairwise.cons ?_ (List.Pairwise.cons hs.1 hs.2)
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · subst h; exact hxy
      · exact prioB_trans hxy (hs.1 z h)
    · rename_i hxy
      refine List.Pairwise.cons ?_ (ih hs.2 (fun z hz => hx z (List.mem_cons_of_mem _ hz)))
      intro z hz
      rcases mem_insLevel.mp hz with h | h
      · subst h
        exact prioB_total (fun e => hx y List.mem_cons_self (by omega)) hxy
      · exact hs.1 z h

theorem sortLevels_pairwise {t : Tree} {xs : List PriceLevel}
    (hd : xs.Pairwise (fun a b => a.price ≠ b.price)) :
    (sortLevels t xs).Pairwise (LvPrio t) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    rw [List.pairwise_cons] at hd
    exact insLevel_pairwise (ih hd.2) (fun y hy => hd.1 y (mem_sortLevels.mp hy))

private theorem bidsSorted_of_pairwise :
    ∀ {l : List PriceLevel}, l.Pairwise (LvPrio .bids) → bidsSortedDescB l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    rw [List.pairwise_cons] at h
    have hab := h.1 b List.mem_cons_self
    have ih := bidsSorted_of_pairwise h.2
    simp only [LvPrio, prioB, decide_eq_true_eq] at hab
    simp [bidsSortedDescB, hab, ih]

private theorem asksSorted_of_pairwise :
    ∀ {l : List PriceLevel}, l.Pairwise (LvPrio .asks) → asksSortedAscB l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    rw [List.pairwise_cons] at h
    have hab := h.1 b List.mem_cons_self
    have ih := asksSorted_of_pairwise h.2
    simp only [LvPrio, prioB, decide_eq_true_eq] at hab
    simp [asksSortedAscB, hab, ih]

/-- Levels of one tree have pairwise distinct prices (`Db.WF.tree_prices`). -/
private theorem tree_levels_distinct {db : Db} (hw : db.WF) (t : Tree) :
    ((db.tree t).map (absLevel db t)).Pairwise (fun a b => a.price ≠ b.price) := by
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (hw.tree_nodup t)
  intro a b ha hb hne heq
  exact hne (hw.tree_prices t a ha b hb (UInt64.toNat_inj.mp heq))

theorem absSide_pairwise {db : Db} (hw : db.WF) (t : Tree) :
    (absSide db t).Pairwise (LvPrio t) :=
  sortLevels_pairwise (tree_levels_distinct hw t)

theorem mem_absSide {db : Db} {t : Tree} {l : PriceLevel} (hl : l ∈ absSide db t) :
    ∃ lh ∈ db.tree t, l = absLevel db t lh := by
  unfold absSide at hl
  obtain ⟨lh, hlh, e⟩ := List.mem_map.mp (mem_sortLevels.mp hl)
  exact ⟨lh, hlh, e.symm⟩

-- ----------------------------------------------------------------------------
-- Queues
-- ----------------------------------------------------------------------------

theorem mem_absQueue {db : Db} {t : Tree} {o : Order} :
    ∀ {i : Nat} {hs : List OrderH}, o ∈ absQueue db t i hs →
      ∃ h ∈ hs, ∃ j, i ≤ j ∧ j < i + hs.length ∧
        o = restingOrder t ((db.orders h).getD OrderRow.dflt) j
  | _, [], ho => by cases ho
  | i, h :: hs, ho => by
    rcases List.mem_cons.mp ho with e | ho
    · exact ⟨h, List.mem_cons_self, i, Nat.le_refl _, by simp, e⟩
    · obtain ⟨h', hh', j, hj1, hj2, e⟩ := mem_absQueue ho
      exact ⟨h', List.mem_cons_of_mem _ hh', j, by omega, by simp; omega, e⟩

theorem absQueue_fifo {db : Db} {t : Tree} :
    ∀ (i : Nat) (hs : List OrderH), FIFOLevel (absQueue db t i hs)
  | _, [] => List.Pairwise.nil
  | i, h :: hs => by
    refine List.Pairwise.cons ?_ (absQueue_fifo (i + 1) hs)
    intro o ho
    obtain ⟨_, _, j, hj, _, e⟩ := mem_absQueue ho
    subst e
    show i < j
    omega

theorem absQueue_ne_nil {db : Db} {t : Tree} {i : Nat} {hs : List OrderH}
    (h : hs ≠ []) : absQueue db t i hs ≠ [] := by
  cases hs with
  | nil => exact absurd rfl h
  | cons _ _ => simp [absQueue]

private theorem le_sum_map_of_mem {f : Nat → Nat} :
    ∀ {l : List Nat} {a : Nat}, a ∈ l → f a ≤ (l.map f).sum
  | [], _, h => by cases h
  | x :: xs, a, h => by
    rcases List.mem_cons.mp h with e | h
    · subst e; simp
    · have := le_sum_map_of_mem (f := f) h; simp; omega

/-- What `ClientInv` says about any order of the abstract book. -/
theorem absBook_order {db : Db} (hc : ClientInv db) {t : Tree} {l : PriceLevel} {o : Order}
    (hl : l ∈ absSide db t) (ho : o ∈ l.orders) :
    ∃ lh ∈ db.tree t, l = absLevel db t lh ∧ ∃ r j,
      r.price = db.levelPrice lh ∧ 0 < r.remaining ∧ j < restingCount db ∧
      o = restingOrder t r j := by
  obtain ⟨lh, hlh, rfl⟩ := mem_absSide hl
  obtain ⟨h, hh, j, -, hj, e⟩ := mem_absQueue ho
  obtain ⟨r, hr, -, hpr, hrem, -, -⟩ := hc.order_ok t lh hlh h hh
  rw [hr] at e
  refine ⟨lh, hlh, rfl, r, j, hpr, hrem, ?_, e⟩
  have hmem : lh ∈ db.tree .bids ++ db.tree .asks := by
    cases t
    · exact List.mem_append_left _ hlh
    · exact List.mem_append_right _ hlh
  have h2 : (db.queue lh).length ≤ restingCount db :=
    le_sum_map_of_mem (f := fun l => (db.queue l).length) hmem
  omega

/-- Every order of `absBook db` rests at its level's price, on its tree's side. -/
theorem absBook_level_consistent {db : Db} (hc : ClientInv db) (t : Tree)
    {l : PriceLevel} (hl : l ∈ absSide db t) {o : Order} (ho : o ∈ l.orders) :
    o.price = some l.price ∧ o.side = sideOfTree t := by
  obtain ⟨lh, -, rfl, r, j, hpr, -, -, rfl⟩ := absBook_order hc hl ho
  simp [restingOrder, absLevel, hpr]

/-- Per-order facts of `RestOk`. -/
private theorem absBook_RestOk {db : Db} (hc : ClientInv db) {t : Tree} {l : PriceLevel}
    (hl : l ∈ absSide db t) {o : Order} (ho : o ∈ l.orders) :
    RestOk (restingCount db + 1) o := by
  obtain ⟨lh, -, -, r, j, -, hrem, hj, rfl⟩ := absBook_order hc hl ho
  have : 0 < r.remaining.toNat := by
    have := (UInt64.lt_iff_toNat_lt (a := 0) (b := r.remaining)).mp hrem; simpa using this
  refine ⟨this, ?_, by simp [restingOrder], by simp [restingOrder], rfl, ?_⟩
  · simp only [restingOrder]; split <;> simp
  · show j < restingCount db + 1; omega

private theorem absSide_SideOk {db : Db} (hc : ClientInv db) (t : Tree) :
    SideOk (restingCount db + 1) (absSide db t) := by
  intro l hl
  obtain ⟨lh, hlh, rfl⟩ := mem_absSide hl
  exact ⟨absQueue_ne_nil (hc.level_nonempty t lh hlh), absQueue_fifo 0 _,
    fun o ho => absBook_RestOk hc hl ho⟩

theorem absBook_uncrossed {db : Db} (hc : ClientInv db) : BookUncrossed (absBook db) := by
  unfold BookUncrossed bestBidPrice bestAskPrice
  show match (absSide db .bids).head?.map (·.price), (absSide db .asks).head?.map (·.price) with
    | some bid, some ask => bid < ask
    | _, _ => True
  cases hb : (absSide db .bids).head? with
  | none => simp
  | some lb =>
    cases ha : (absSide db .asks).head? with
    | none => simp
    | some la =>
      simp only [Option.map]
      obtain ⟨b, hb', rfl⟩ := mem_absSide (List.mem_of_mem_head? hb)
      obtain ⟨a, ha', rfl⟩ := mem_absSide (List.mem_of_mem_head? ha)
      exact UInt64.lt_iff_toNat_lt.mp (hc.uncrossed b hb' a ha')

-- ----------------------------------------------------------------------------
-- Main theorems
-- ----------------------------------------------------------------------------

/-- INV-2/3/4 (`AllInv`) of the abstract book. -/
theorem absBook_AllInv {db : Db} (hc : ClientInv db) (hw : db.WF) : AllInv (absBook db) :=
  ⟨absBook_uncrossed hc,
   bidsSorted_of_pairwise (absSide_pairwise hw .bids),
   asksSorted_of_pairwise (absSide_pairwise hw .asks)⟩

/-- The structural bundle `BookOk` (INV-1, 5, 6, 7, 8, 13, 14 plus timestamps
    below the clock) of the abstract book. -/
theorem absBook_BookOk {db : Db} (hc : ClientInv db) : BookOk (absBook db) :=
  ⟨absSide_SideOk hc .bids, absSide_SideOk hc .asks⟩

/-- The full §13 book-state suite of the abstract book. -/
theorem absBook_BookInvariant {db : Db} (hc : ClientInv db) (_hw : db.WF) :
    BookInvariant (absBook db) := by
  obtain ⟨hne, hng, hsc, hfifo, hnm, hnmtl, hnmq⟩ :=
    FullBookInv_of_BookOkAt (absBook_BookOk hc)
  exact ⟨absBook_uncrossed hc, hng, hsc, hnm, hnmtl, hnmq, hne, hfifo⟩

/-- The whole precondition bundle of `process` holds on the abstract book. -/
theorem absBook_ProcessInv {db : Db} (hc : ClientInv db) (hw : db.WF) :
    ProcessInv (absBook db) :=
  by
  unfold ProcessInv
  refine ⟨absBook_AllInv hc hw, absBook_BookOk hc, ?_, ?_⟩ <;>
    (intro s hs; simp [absBook] at hs)

/-- The statement asked for in Prompt 3. -/
theorem absBook_invariants {db : Db} (h : ClientInv db ∧ db.WF) :
    AllInv (absBook db) ∧ BookInvariant (absBook db) :=
  ⟨absBook_AllInv h.1 h.2, absBook_BookInvariant h.1 h.2⟩

theorem ClientInv_WF_empty : ClientInv Db.empty ∧ Db.empty.WF :=
  ⟨ClientInv_empty, WF_empty⟩

end EngineDbAbs
