/-!
# EngineDb API Specification

The abstract contract of the generated EngineDb layer
(`c/include/matching_engine_gen.h`), stated without any memory model.
The matching logic in `c/src/matching_engine.c` is meant to be verified
against this file only; the generated C is separately proved to implement it.

## Abstract state

The database is a relational store of two row types, `Order` and
`PriceLevel`, plus four indexes over them:

| C structure              | abstract view                          |
| ------------------------ | -------------------------------------- |
| `order_pool` (Tpool)     | `orders : OrderH → Option OrderRow`    |
| `level_pool` (Tpool)     | `levels : LevelH → Option LevelRow`    |
| `PriceLevel.orders` (Llist) | `queue : LevelH → List OrderH`      |
| `ind_order` (Thash)      | `hash : List OrderH`                   |
| `bids`, `asks` (Atree)   | `tree : Tree → List LevelH`            |

Handles (`OrderH`, `LevelH`) stand for pointers. A handle is *live* while its
row is allocated. Freeing a row kills its handle, and allocation may hand the
same handle out again, exactly like `malloc` reusing an address. So a stale
handle can alias a newer row; the client proof must not keep handles across a
free. (`MatchingEngine_CancelOrder` currently reads `ord->side` after
`EngineDb_order_pool_Free(ord)`: that call has no valid precondition here.)

## Contract shape

Each operation has a precondition `pre` and a postcondition `post`. Calling
an operation outside `pre` is undefined behaviour: the client must prove
`pre` at every call site. `post` relates the state before and after and the
returned value. Allocation is the only nondeterministic operation: it may
fail (`none`, state unchanged) at any time, modelling `malloc` returning NULL.

## `total_qty`

`PriceLevel.totalQty` is maintained by the generated queue operations:
`InsertTail` adds the order's remaining quantity and `Remove` subtracts it.
A fill changes an order's remaining quantity in place, and no generated
operation covers that, so the client adjusts `totalQty` itself on fills and
only then. Writing it on any other path double-counts (divergence D7).

## Key fields

A field that an index is keyed on can only be written while the row is not
in that index: `Order.id` while not in `hash`, `PriceLevel.price` while not in
either tree. Other fields are payload and can be written freely.
-/

namespace EngineDbApi

abbrev OrderH := Nat
abbrev LevelH := Nat

/-- The client-visible fields of `struct Order`. Link fields are not visible. -/
structure OrderRow where
  id        : UInt64
  account   : UInt64
  side      : UInt8
  stpMode   : UInt8
  price     : UInt64
  qty       : UInt64
  remaining : UInt64
  deriving DecidableEq, Repr

/-- The client-visible fields of `struct PriceLevel`. -/
structure LevelRow where
  price    : UInt64
  totalQty : UInt64
  deriving DecidableEq, Repr

/-- Which price tree. -/
inductive Tree where
  | bids
  | asks
  deriving DecidableEq, Repr

structure Db where
  orders : OrderH → Option OrderRow
  levels : LevelH → Option LevelRow
  queue  : LevelH → List OrderH
  hash   : List OrderH
  tree   : Tree → List LevelH

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

@[simp] theorem upd_other {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β)
    (h : x ≠ a) : upd f a b x = f x := by simp [upd, h]

def Db.empty : Db :=
  { orders := fun _ => none, levels := fun _ => none, queue := fun _ => [],
    hash := [], tree := fun _ => [] }

def Db.orderLive (db : Db) (h : OrderH) : Prop := (db.orders h).isSome
def Db.levelLive (db : Db) (l : LevelH) : Prop := (db.levels l).isSome

/-- The order `h` is linked into some level's queue. -/
def Db.queued (db : Db) (h : OrderH) : Prop := ∃ l, h ∈ db.queue l

/-- Price of a level handle, `0` if dead. Only used on live handles. -/
def Db.levelPrice (db : Db) (l : LevelH) : UInt64 :=
  ((db.levels l).map LevelRow.price).getD 0

/-- Id of an order handle, `0` if dead. Only used on live handles. -/
def Db.orderId (db : Db) (h : OrderH) : UInt64 :=
  ((db.orders h).map OrderRow.id).getD 0

/-- `better t p q`: price `p` has priority over `q` in tree `t`. -/
def better : Tree → UInt64 → UInt64 → Prop
  | .bids, p, q => q ≤ p
  | .asks, p, q => p ≤ q

/-- Representation invariant of the abstract store. Every operation preserves
    it when called within its precondition (`*_preserves_WF` below). -/
structure Db.WF (db : Db) : Prop where
  queue_live   : ∀ l h, h ∈ db.queue l → db.orderLive h ∧ db.levelLive l
  queue_nodup  : ∀ l, (db.queue l).Nodup
  queue_unique : ∀ l₁ l₂ h, h ∈ db.queue l₁ → h ∈ db.queue l₂ → l₁ = l₂
  hash_live    : ∀ h ∈ db.hash, db.orderLive h
  hash_nodup   : db.hash.Nodup
  hash_ids     : ∀ h₁ ∈ db.hash, ∀ h₂ ∈ db.hash, db.orderId h₁ = db.orderId h₂ → h₁ = h₂
  tree_live    : ∀ t, ∀ l ∈ db.tree t, db.levelLive l
  tree_nodup   : ∀ t, (db.tree t).Nodup
  tree_disjoint : ∀ l, l ∈ db.tree .bids → l ∈ db.tree .asks → False
  tree_prices  : ∀ t, ∀ l₁ ∈ db.tree t, ∀ l₂ ∈ db.tree t,
                   db.levelPrice l₁ = db.levelPrice l₂ → l₁ = l₂

-- ============================================================================
-- Pools (Tpool): `EngineDb_order_pool_Alloc/Free`, `EngineDb_level_pool_Alloc/Free`
-- ============================================================================

/-- `EngineDb_order_pool_Alloc`. Either fails with the state unchanged, or
    returns a handle that was not live, now live with unspecified contents. -/
def orderAlloc.post (db : Db) (r : Option OrderH) (db' : Db) : Prop :=
  match r with
  | none   => db' = db
  | some h => db.orders h = none ∧
      ∃ row, db' = { db with orders := upd db.orders h (some row) }

/-- `EngineDb_order_pool_Free`: the row must be unlinked from every index. -/
def orderFree.pre (db : Db) (h : OrderH) : Prop :=
  db.orderLive h ∧ ¬ db.queued h ∧ h ∉ db.hash

def orderFree.post (db : Db) (h : OrderH) (db' : Db) : Prop :=
  db' = { db with orders := upd db.orders h none }

/-- `EngineDb_level_pool_Alloc`. -/
def levelAlloc.post (db : Db) (r : Option LevelH) (db' : Db) : Prop :=
  match r with
  | none   => db' = db
  | some l => db.levels l = none ∧
      ∃ row, db' = { db with levels := upd db.levels l (some row) }

/-- `EngineDb_level_pool_Free`: the level must be out of both trees and empty. -/
def levelFree.pre (db : Db) (l : LevelH) : Prop :=
  db.levelLive l ∧ l ∉ db.tree .bids ∧ l ∉ db.tree .asks ∧ db.queue l = []

def levelFree.post (db : Db) (l : LevelH) (db' : Db) : Prop :=
  db' = { db with levels := upd db.levels l none }

-- ============================================================================
-- Field access through a handle (`ord->remaining_qty`, `lvl->price`, ...)
-- ============================================================================

/-- Reading `*ord`: only on a live handle. -/
def readOrder.pre (db : Db) (h : OrderH) : Prop := db.orderLive h

/-- Writing `*ord`: live handle; `id` is frozen while the row is in `hash`. -/
def writeOrder.pre (db : Db) (h : OrderH) (row : OrderRow) : Prop :=
  ∃ old, db.orders h = some old ∧ (h ∈ db.hash → row.id = old.id)

def writeOrder.post (db : Db) (h : OrderH) (row : OrderRow) (db' : Db) : Prop :=
  db' = { db with orders := upd db.orders h (some row) }

def readLevel.pre (db : Db) (l : LevelH) : Prop := db.levelLive l

/-- Writing `*lvl`: live handle; `price` is frozen while the level is in a tree. -/
def writeLevel.pre (db : Db) (l : LevelH) (row : LevelRow) : Prop :=
  ∃ old, db.levels l = some old ∧
    ((l ∈ db.tree .bids ∨ l ∈ db.tree .asks) → row.price = old.price)

def writeLevel.post (db : Db) (l : LevelH) (row : LevelRow) (db' : Db) : Prop :=
  db' = { db with levels := upd db.levels l (some row) }

/-- `lvl->orders_n`: generated bookkeeping, read-only for the client. -/
def levelCount (db : Db) (l : LevelH) : Nat := (db.queue l).length

/-- `ord->p_price_level`: the level whose queue holds `h`, if any. -/
def owner.post (db : Db) (h : OrderH) (r : Option LevelH) : Prop :=
  match r with
  | none   => ¬ db.queued h
  | some l => h ∈ db.queue l

-- ============================================================================
-- Order hash index (Thash): `EngineDb_ind_order_Find/InsertMaybe/Remove`
-- ============================================================================

/-- `EngineDb_ind_order_Find`. -/
def hashFind.post (db : Db) (id : UInt64) (r : Option OrderH) : Prop :=
  match r with
  | none   => ∀ h ∈ db.hash, db.orderId h ≠ id
  | some h => h ∈ db.hash ∧ db.orderId h = id

def hashInsert.pre (db : Db) (h : OrderH) : Prop := db.orderLive h ∧ h ∉ db.hash

/-- `EngineDb_ind_order_InsertMaybe`: refuses a duplicate id. -/
def hashInsert.post (db : Db) (h : OrderH) (ok : Bool) (db' : Db) : Prop :=
  if ∃ h' ∈ db.hash, db.orderId h' = db.orderId h then
    ok = false ∧ db' = db
  else
    ok = true ∧ db' = { db with hash := h :: db.hash }

def hashRemove.pre (db : Db) (h : OrderH) : Prop := h ∈ db.hash

def hashRemove.post (db : Db) (h : OrderH) (db' : Db) : Prop :=
  db' = { db with hash := db.hash.erase h }

-- ============================================================================
-- FIFO queue per level (Llist): `PriceLevel_orders_*`
-- ============================================================================

def qInsertTail.pre (db : Db) (l : LevelH) (h : OrderH) : Prop :=
  db.levelLive l ∧ db.orderLive h ∧ ¬ db.queued h

/-- Remaining quantity of an order handle, `0` if dead. -/
def Db.orderRemaining (db : Db) (h : OrderH) : UInt64 :=
  ((db.orders h).map OrderRow.remaining).getD 0

/-- Apply `f` to the `totalQty` of level `l`. -/
def Db.mapTotal (db : Db) (l : LevelH) (f : UInt64 → UInt64) : LevelH → Option LevelRow :=
  upd db.levels l ((db.levels l).map fun r => { r with totalQty := f r.totalQty })

/-- `PriceLevel_orders_InsertTail`. Also adds the order's remaining quantity
    to the level's `total_qty` (wrapping, as `uint64_t` does). -/
def qInsertTail.post (db : Db) (l : LevelH) (h : OrderH) (db' : Db) : Prop :=
  db' = { db with queue := upd db.queue l (db.queue l ++ [h]),
                  levels := db.mapTotal l (· + db.orderRemaining h) }

def qRemove.pre (db : Db) (l : LevelH) (h : OrderH) : Prop := h ∈ db.queue l

/-- `PriceLevel_orders_Remove`. Also subtracts the order's remaining quantity
    from the level's `total_qty`, stopping at `0` rather than wrapping. -/
def qRemove.post (db : Db) (l : LevelH) (h : OrderH) (db' : Db) : Prop :=
  db' = { db with queue := upd db.queue l ((db.queue l).erase h),
                  levels := db.mapTotal l
                    (fun t => if db.orderRemaining h ≤ t then t - db.orderRemaining h else 0) }

/-- `PriceLevel_orders_First`. -/
def qFirst.pre (db : Db) (l : LevelH) : Prop := db.levelLive l

def qFirst.post (db : Db) (l : LevelH) (r : Option OrderH) : Prop :=
  r = (db.queue l).head?

/-- The element after `x` in `xs`. -/
def nextIn : List Nat → Nat → Option Nat
  | [], _ => none
  | [_], _ => none
  | a :: b :: rest, x => if a = x then some b else nextIn (b :: rest) x

/-- `PriceLevel_orders_Next`. -/
def qNext.pre (db : Db) (h : OrderH) : Prop := db.queued h

def qNext.post (db : Db) (h : OrderH) (r : Option OrderH) : Prop :=
  ∃ l, h ∈ db.queue l ∧ r = nextIn (db.queue l) h

-- ============================================================================
-- Price trees (Atree): `EngineDb_{bids,asks}_Find/Insert/Remove/Best`
-- ============================================================================

/-- `EngineDb_{bids,asks}_Find`. -/
def tFind.post (db : Db) (t : Tree) (p : UInt64) (r : Option LevelH) : Prop :=
  match r with
  | none   => ∀ l ∈ db.tree t, db.levelPrice l ≠ p
  | some l => l ∈ db.tree t ∧ db.levelPrice l = p

/-- `EngineDb_{bids,asks}_Insert`: the price must not already be present. -/
def tInsert.pre (db : Db) (t : Tree) (l : LevelH) : Prop :=
  db.levelLive l ∧ l ∉ db.tree .bids ∧ l ∉ db.tree .asks ∧
    ∀ l' ∈ db.tree t, db.levelPrice l' ≠ db.levelPrice l

def tInsert.post (db : Db) (t : Tree) (l : LevelH) (db' : Db) : Prop :=
  db' = { db with tree := upd db.tree t (l :: db.tree t) }

def tRemove.pre (db : Db) (t : Tree) (l : LevelH) : Prop := l ∈ db.tree t

def tRemove.post (db : Db) (t : Tree) (l : LevelH) (db' : Db) : Prop :=
  db' = { db with tree := upd db.tree t ((db.tree t).erase l) }

/-- `EngineDb_{bids,asks}_Best`: highest bid or lowest ask. -/
def tBest.post (db : Db) (t : Tree) (r : Option LevelH) : Prop :=
  match r with
  | none   => db.tree t = []
  | some l => l ∈ db.tree t ∧ ∀ l' ∈ db.tree t, better t (db.levelPrice l) (db.levelPrice l')

end EngineDbApi
