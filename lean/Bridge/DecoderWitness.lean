import Amcc.Interface
import Amcc.Spec.Algebra
import Amcc.CSubset.Value
import Bridge.MatchingEngineBridge
import Bridge.RelationalMemory

/-!
# Decoder Witness: Concrete Memory Decoding Tests

This module proves that `alpha_concrete` and the relational decoders:
1. Decode valid AMCC C memory structures into abstract `BookState` values (`:= rfl`).
2. Correctly propagate `none` on type errors, corrupt fields, dangling pointers, and fuel exhaustion (`:= rfl`).
-/

namespace VerifiedCMatchingEngine

open CSubset

/-! ## 1. Valid Memory Configurations -/

/-- Empty memory decoding to empty book -/
def m_empty : Mem :=
  { glb := [], hp := [], next := 1 }

example : alpha_concrete m_empty none none = some { bids := [], asks := [] } := rfl

/-- Concrete Order in Heap Block 1 -/
def orderBlock1 : Nat × Value :=
  (1, Value.strct [
    ("id", Value.u64 1),
    ("account_id", Value.u64 42),
    ("price", Value.u64 100),
    ("remaining_qty", Value.u64 10),
    ("side", Value.u8 0),
    ("orders_next", Value.null)
  ])

/-- Concrete PriceLevel in Heap Block 2 -/
def priceLevelBlock2 : Nat × Value :=
  (2, Value.strct [
    ("price", Value.u64 100),
    ("orders_head", Value.ptr ⟨Root.blk 1, []⟩),
    ("tree_left", Value.null),
    ("tree_right", Value.null)
  ])

/-- Valid Memory with single bid order at price 100 -/
def m_valid_single : Mem :=
  { glb := [],
    hp := [orderBlock1, priceLevelBlock2],
    next := 3 }

def expected_order1 : Order :=
  { id := 1, account := 42, price := 100, qty := 10, side := Side.buy }

def expected_level2 : PriceLevel :=
  { price := 100, orders := [expected_order1] }

def expected_book_single : BookState :=
  { bids := [expected_level2], asks := [] }

example : decodeOrder m_valid_single ⟨Root.blk 1, []⟩ = some expected_order1 := rfl

example : decodeOrderList m_valid_single (some ⟨Root.blk 1, []⟩) = some [expected_order1] := rfl

example : decodePriceLevel m_valid_single ⟨Root.blk 2, []⟩ = some expected_level2 := rfl

example : alpha_concrete m_valid_single (some ⟨Root.blk 2, []⟩) none = some expected_book_single := rfl


/-! ## 2. Corrupt Memory Configurations (Partiality & Failure Proofs) -/

/-- Corrupt memory: `price` field in order is a boolean instead of u64 -/
def orderBlock_bad_type : Nat × Value :=
  (1, Value.strct [
    ("id", Value.u64 1),
    ("account_id", Value.u64 42),
    ("price", Value.bool true),  -- type error!
    ("remaining_qty", Value.u64 10),
    ("side", Value.u8 0),
    ("orders_next", Value.null)
  ])

def m_corrupt_type : Mem :=
  { glb := [], hp := [orderBlock_bad_type, priceLevelBlock2], next := 3 }

-- Order decoding fails cleanly
example : decodeOrder m_corrupt_type ⟨Root.blk 1, []⟩ = none := rfl

-- Alpha abstraction returns none rather than silently defaulting
example : alpha_concrete m_corrupt_type (some ⟨Root.blk 2, []⟩) none = none := rfl


/-- Corrupt memory: `orders_head` points to dangling/unmapped block 99 -/
def priceLevelBlock_dangling : Nat × Value :=
  (2, Value.strct [
    ("price", Value.u64 100),
    ("orders_head", Value.ptr ⟨Root.blk 99, []⟩),  -- dangling pointer!
    ("tree_left", Value.null),
    ("tree_right", Value.null)
  ])

def m_dangling_ptr : Mem :=
  { glb := [], hp := [orderBlock1, priceLevelBlock_dangling], next := 3 }

-- Price level decoding fails cleanly
example : decodePriceLevel m_dangling_ptr ⟨Root.blk 2, []⟩ = none := rfl

-- Alpha abstraction returns none
example : alpha_concrete m_dangling_ptr (some ⟨Root.blk 2, []⟩) none = none := rfl


/-- Corrupt memory: `tree_left` contains scalar u32 instead of pointer or null -/
def priceLevelBlock_bad_tree : Nat × Value :=
  (2, Value.strct [
    ("price", Value.u64 100),
    ("orders_head", Value.ptr ⟨Root.blk 1, []⟩),
    ("tree_left", Value.u32 999),  -- invalid pointer value!
    ("tree_right", Value.null)
  ])

def m_corrupt_tree : Mem :=
  { glb := [], hp := [orderBlock1, priceLevelBlock_bad_tree], next := 3 }

-- Price levels tree traversal fails cleanly
example : decodePriceLevels m_corrupt_tree (some ⟨Root.blk 2, []⟩) = none := rfl

-- Alpha abstraction returns none
example : alpha_concrete m_corrupt_tree (some ⟨Root.blk 2, []⟩) none = none := rfl


/-- Fuel exhaustion strictly fails (returns none) -/
example : decodeOrderListAux m_valid_single 0 (some ⟨Root.blk 1, []⟩) = none := rfl
example : decodePriceLevelsAux m_valid_single 0 (some ⟨Root.blk 2, []⟩) = none := rfl

end VerifiedCMatchingEngine
