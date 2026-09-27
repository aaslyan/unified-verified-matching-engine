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

## Level totals

`PriceLevel.total_qty` is not part of this contract. No in-scope matcher path
reads a total, and the one bug found in this area (divergence D7, a double
subtraction) came from two parties writing it. Totals, if a data layer keeps
them, are its private state: it maintains them itself, including when the
matcher changes an order's remaining quantity through `writeOrder`.

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
  /-- The live order handles, as a finite list (pool usage). -/
  oLive  : List OrderH
  /-- The live level handles, as a finite list (pool usage). -/
  lLive  : List LevelH

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

@[simp] theorem upd_other {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β)
    (h : x ≠ a) : upd f a b x = f x := by simp [upd, h]

def Db.empty : Db :=
  { orders := fun _ => none, levels := fun _ => none, queue := fun _ => [],
    hash := [], tree := fun _ => [], oLive := [], lLive := [] }

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
  orders_live  : ∀ h, db.orderLive h ↔ h ∈ db.oLive
  oLive_nodup  : db.oLive.Nodup
  levels_live  : ∀ l, db.levelLive l ↔ l ∈ db.lLive
  lLive_nodup  : db.lLive.Nodup

/-- Order pool usage: the number of live order rows (`order_pool_n`). -/
def Db.count (db : Db) : Nat := db.oLive.length

/-- Level pool usage: the number of live level rows (`level_pool_n`). -/
def Db.levelUsed (db : Db) : Nat := db.lLive.length

-- ============================================================================
-- Pools (Tpool): `EngineDb_order_pool_Alloc/Free`, `EngineDb_level_pool_Alloc/Free`
-- ============================================================================

/-- `EngineDb_order_pool_Alloc`. Either fails with the state unchanged, or
    returns a handle that was not live, now live with unspecified contents. -/
def orderAlloc.post (db : Db) (r : Option OrderH) (db' : Db) : Prop :=
  match r with
  | none   => db' = db
  | some h => db.orders h = none ∧
      ∃ row, db' = { db with orders := upd db.orders h (some row), oLive := h :: db.oLive }

/-- `EngineDb_order_pool_Free`: the row must be unlinked from every index. -/
def orderFree.pre (db : Db) (h : OrderH) : Prop :=
  db.orderLive h ∧ ¬ db.queued h ∧ h ∉ db.hash

def orderFree.post (db : Db) (h : OrderH) (db' : Db) : Prop :=
  db' = { db with orders := upd db.orders h none, oLive := db.oLive.erase h }

/-- `EngineDb_level_pool_Alloc`. -/
def levelAlloc.post (db : Db) (r : Option LevelH) (db' : Db) : Prop :=
  match r with
  | none   => db' = db
  | some l => db.levels l = none ∧
      ∃ row, db' = { db with levels := upd db.levels l (some row), lLive := l :: db.lLive }

/-- `EngineDb_level_pool_Free`: the level must be out of both trees and empty. -/
def levelFree.pre (db : Db) (l : LevelH) : Prop :=
  db.levelLive l ∧ l ∉ db.tree .bids ∧ l ∉ db.tree .asks ∧ db.queue l = []

def levelFree.post (db : Db) (l : LevelH) (db' : Db) : Prop :=
  db' = { db with levels := upd db.levels l none, lLive := db.lLive.erase l }

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

/-- `PriceLevel_orders_InsertTail`. -/
def qInsertTail.post (db : Db) (l : LevelH) (h : OrderH) (db' : Db) : Prop :=
  db' = { db with queue := upd db.queue l (db.queue l ++ [h]) }

def qRemove.pre (db : Db) (l : LevelH) (h : OrderH) : Prop := h ∈ db.queue l

/-- `PriceLevel_orders_Remove`. -/
def qRemove.post (db : Db) (l : LevelH) (h : OrderH) (db' : Db) : Prop :=
  db' = { db with queue := upd db.queue l ((db.queue l).erase h) }

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

-- ============================================================================
-- The store as a parameter (plan v2 §2, §4)
-- ============================================================================

/-- A storage layer for the matcher: the operations as functions, a view onto
    the abstract store `Db`, and laws stating that each operation, called
    within its precondition on a well-formed store, meets its contract.

    `capacity` bounds each pool. Allocation fails exactly when the pool is
    full, and then leaves the store unchanged (§4 "Capacity"). A matcher
    verified against this class knows nothing else about memory. -/
class EngineDb (S : Type) where
  capacity : Nat
  view : S → Db
  init : S
  orderAlloc : S → Option OrderH × S
  orderFree : S → OrderH → S
  levelAlloc : S → Option LevelH × S
  levelFree : S → LevelH → S
  readOrder : S → OrderH → Option OrderRow
  writeOrder : S → OrderH → OrderRow → S
  readLevel : S → LevelH → Option LevelRow
  writeLevel : S → LevelH → LevelRow → S
  levelCount : S → LevelH → Nat
  owner : S → OrderH → Option LevelH
  hashFind : S → UInt64 → Option OrderH
  hashInsert : S → OrderH → Bool × S
  hashRemove : S → OrderH → S
  qInsertTail : S → LevelH → OrderH → S
  qRemove : S → LevelH → OrderH → S
  qFirst : S → LevelH → Option OrderH
  qNext : S → OrderH → Option OrderH
  tFind : S → Tree → UInt64 → Option LevelH
  tInsert : S → Tree → LevelH → S
  tRemove : S → Tree → LevelH → S
  tBest : S → Tree → Option LevelH
  /-- Live order rows (`order_pool_n`). -/
  count : S → Nat
  /-- Live level rows (`level_pool_n`). -/
  levelsUsed : S → Nat
  init_view : view init = Db.empty
  init_count : count init = 0
  init_levelsUsed : levelsUsed init = 0
  orderAlloc_law : ∀ s, (view s).WF →
    EngineDbApi.orderAlloc.post (view s) (orderAlloc s).1 (view (orderAlloc s).2) ∧
    ((orderAlloc s).1 = none ↔ capacity ≤ count s)
  orderFree_law : ∀ s h, (view s).WF → EngineDbApi.orderFree.pre (view s) h →
    EngineDbApi.orderFree.post (view s) h (view (orderFree s h))
  levelAlloc_law : ∀ s, (view s).WF →
    EngineDbApi.levelAlloc.post (view s) (levelAlloc s).1 (view (levelAlloc s).2) ∧
    ((levelAlloc s).1 = none ↔ capacity ≤ levelsUsed s)
  levelFree_law : ∀ s l, (view s).WF → EngineDbApi.levelFree.pre (view s) l →
    EngineDbApi.levelFree.post (view s) l (view (levelFree s l))
  readOrder_law : ∀ s h, readOrder s h = (view s).orders h
  writeOrder_law : ∀ s h row, (view s).WF → EngineDbApi.writeOrder.pre (view s) h row →
    EngineDbApi.writeOrder.post (view s) h row (view (writeOrder s h row))
  readLevel_law : ∀ s l, readLevel s l = (view s).levels l
  writeLevel_law : ∀ s l row, (view s).WF → EngineDbApi.writeLevel.pre (view s) l row →
    EngineDbApi.writeLevel.post (view s) l row (view (writeLevel s l row))
  levelCount_law : ∀ s l, levelCount s l = EngineDbApi.levelCount (view s) l
  owner_law : ∀ s h, (view s).WF → EngineDbApi.owner.post (view s) h (owner s h)
  hashFind_law : ∀ s id, (view s).WF → EngineDbApi.hashFind.post (view s) id (hashFind s id)
  hashInsert_law : ∀ s h, (view s).WF → EngineDbApi.hashInsert.pre (view s) h →
    EngineDbApi.hashInsert.post (view s) h (hashInsert s h).1 (view (hashInsert s h).2)
  hashRemove_law : ∀ s h, (view s).WF → EngineDbApi.hashRemove.pre (view s) h →
    EngineDbApi.hashRemove.post (view s) h (view (hashRemove s h))
  qInsertTail_law : ∀ s l h, (view s).WF → EngineDbApi.qInsertTail.pre (view s) l h →
    EngineDbApi.qInsertTail.post (view s) l h (view (qInsertTail s l h))
  qRemove_law : ∀ s l h, (view s).WF → EngineDbApi.qRemove.pre (view s) l h →
    EngineDbApi.qRemove.post (view s) l h (view (qRemove s l h))
  qFirst_law : ∀ s l, (view s).WF → EngineDbApi.qFirst.pre (view s) l →
    EngineDbApi.qFirst.post (view s) l (qFirst s l)
  qNext_law : ∀ s h, (view s).WF → EngineDbApi.qNext.pre (view s) h →
    EngineDbApi.qNext.post (view s) h (qNext s h)
  tFind_law : ∀ s t p, (view s).WF → EngineDbApi.tFind.post (view s) t p (tFind s t p)
  tInsert_law : ∀ s t l, (view s).WF → EngineDbApi.tInsert.pre (view s) t l →
    EngineDbApi.tInsert.post (view s) t l (view (tInsert s t l))
  tRemove_law : ∀ s t l, (view s).WF → EngineDbApi.tRemove.pre (view s) t l →
    EngineDbApi.tRemove.post (view s) t l (view (tRemove s t l))
  tBest_law : ∀ s t, (view s).WF → EngineDbApi.tBest.post (view s) t (tBest s t)
  -- Pool usage: alloc +1, free −1, every other operation unchanged.
  count_orderAlloc : ∀ s h, (orderAlloc s).1 = some h → count (orderAlloc s).2 = count s + 1
  count_orderFree : ∀ s h, (view s).WF → EngineDbApi.orderFree.pre (view s) h →
    count (orderFree s h) + 1 = count s
  count_levelAlloc : ∀ s, count (levelAlloc s).2 = count s
  count_levelFree : ∀ s l, count (levelFree s l) = count s
  count_writeOrder : ∀ s h row, count (writeOrder s h row) = count s
  count_writeLevel : ∀ s l row, count (writeLevel s l row) = count s
  count_hashInsert : ∀ s h, count (hashInsert s h).2 = count s
  count_hashRemove : ∀ s h, count (hashRemove s h) = count s
  count_qInsertTail : ∀ s l h, count (qInsertTail s l h) = count s
  count_qRemove : ∀ s l h, count (qRemove s l h) = count s
  count_tInsert : ∀ s t l, count (tInsert s t l) = count s
  count_tRemove : ∀ s t l, count (tRemove s t l) = count s
  levelsUsed_levelAlloc : ∀ s l, (levelAlloc s).1 = some l →
    levelsUsed (levelAlloc s).2 = levelsUsed s + 1
  levelsUsed_levelFree : ∀ s l, (view s).WF → EngineDbApi.levelFree.pre (view s) l →
    levelsUsed (levelFree s l) + 1 = levelsUsed s
  levelsUsed_orderAlloc : ∀ s, levelsUsed (orderAlloc s).2 = levelsUsed s
  levelsUsed_orderFree : ∀ s h, levelsUsed (orderFree s h) = levelsUsed s
  levelsUsed_writeOrder : ∀ s h row, levelsUsed (writeOrder s h row) = levelsUsed s
  levelsUsed_writeLevel : ∀ s l row, levelsUsed (writeLevel s l row) = levelsUsed s
  levelsUsed_hashInsert : ∀ s h, levelsUsed (hashInsert s h).2 = levelsUsed s
  levelsUsed_hashRemove : ∀ s h, levelsUsed (hashRemove s h) = levelsUsed s
  levelsUsed_qInsertTail : ∀ s l h, levelsUsed (qInsertTail s l h) = levelsUsed s
  levelsUsed_qRemove : ∀ s l h, levelsUsed (qRemove s l h) = levelsUsed s
  levelsUsed_tInsert : ∀ s t l, levelsUsed (tInsert s t l) = levelsUsed s
  levelsUsed_tRemove : ∀ s t l, levelsUsed (tRemove s t l) = levelsUsed s

end EngineDbApi
