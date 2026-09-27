import Matcher.Print
import Bridge.ProcessB

/-!
# The generated matcher

`MatcherProgram.program` is the matching logic of `c/src/matching_engine.c`
(`MatchingEngine_ProcessOrder`, `MatchingEngine_CancelOrder`) written in the
matcher language, with the plan-v2 §4 changes. `main` prints it; the output
is committed as `c/gen/matcher.c` (`scripts/gen_matcher.sh`).

Structure, following `ProcessB.processB`:

* `gen_process_order` runs the entry checks in `processB`'s order —
  unsupported order type, invalid request (side, STP mode, zero quantity,
  price 0 on a priced type, quantity above `qmax capacity`), duplicate id,
  capacity — then dispatches on the side.
* `gen_process_buy` / `gen_process_sell` are one generator, `sideFun`,
  instantiated for each side. Each first makes the post-only crossing
  decision where `process` makes it (after the entry checks, before any
  trade), then matches against the contra tree, then rests the remainder.
  A level is freed when its last order leaves.
* `gen_cancel_order` is `MatchingEngine_CancelOrder`; it reads the order's side
  before freeing it.

Every loop is bounded by `capacity + 1`: each inner iteration that continues
removes a resting order, and each outer iteration that continues removes a
level. Level totals are not touched: they are not in the contract.
-/

namespace MatcherProgram

open Matcher EngineDbApi ProcessB

-- ============================================================================
-- Codes
-- ============================================================================

def SIDE_BUY : UInt8 := 0
def SIDE_SELL : UInt8 := 1
def OT_LIMIT : UInt8 := 0
def OT_MARKET : UInt8 := 1
def OT_IOC : UInt8 := 2
def OT_POST_ONLY : UInt8 := 3
def STP_NONE : UInt8 := 0
def STP_CANCEL_NEW : UInt8 := 1
def STP_CANCEL_OLD : UInt8 := 2
def STP_CANCEL_BOTH : UInt8 := 3
def STP_DECREMENT : UInt8 := 4

/-- The C value of each result code. -/
def codeOf : ResultCode → UInt8
  | .accepted => 0
  | .cancelled => 1
  | .rejectedUnsupported => 2
  | .rejectedInvalid => 3
  | .rejectedDuplicate => 4
  | .rejectedCapacity => 5
  | .rejectedPostOnly => 6
  | .rejectedUnknownId => 7

-- ============================================================================
-- Syntax helpers
-- ============================================================================

def v (x : Ident) : Expr := .var x
def u (n : UInt64) : Expr := .lit n
def c (n : UInt8) : Expr := .clit n
def b2 (op : BinOp) (a b : Expr) : Expr := .bin op a b
def eqc (x : Ident) (n : UInt8) : Expr := b2 .eq (v x) (c n)
def nec (x : Ident) (n : UInt8) : Expr := b2 .ne (v x) (c n)
def not' (e : Expr) : Expr := .un .not e
def and' (a b : Expr) : Expr := b2 .and a b
def or' (a b : Expr) : Expr := b2 .or a b
def retc (r : ResultCode) : Stmt := .ret (c (codeOf r))
def call0 (op : Ext) (args : List Expr) : Stmt := .ext none op args
def call1 (x : Ident) (op : Ext) (args : List Expr) : Stmt := .ext (some x) op args
def whenS (cond : Expr) (s : Stmt) : Stmt := .ite cond s .skip

/-- `2^64 - 1`. -/
def U64_MAX : UInt64 := 18446744073709551615

/-- `qmax capacity = (2^64 - 1) / (capacity + 1)`, as in `ProcessB.qmax`. -/
def qmaxE : Expr := b2 .div (u U64_MAX) (b2 .add .capacity (u 1))

-- ============================================================================
-- Functions
-- ============================================================================

def minFun : FunDef where
  name := "gen_min_u64"
  params := [("a", .u64), ("b", .u64)]
  locals := []
  ret := .u64
  entry := false
  body := .ite (b2 .lt (v "a") (v "b")) (.ret (v "a")) (.ret (v "b"))

/-- Unlink a resting order from its level, the hash and the pool. -/
def removeResting (lvl o : Ident) : Stmt := Stmt.block [
  call0 .qRemove [v lvl, v o],
  call0 .hashRemove [v o],
  call0 .orderFree [v o]]

/-- One side of `ProcessOrder`. `isBuy`: the incoming order is a buy, so it
    matches the asks and rests on the bids. -/
def sideFun (isBuy : Bool) : FunDef :=
  let contra : Tree := if isBuy then .asks else .bids
  let own : Tree := if isBuy then .bids else .asks
  -- a best contra price `bp` is marketable against limit price `price`
  let crosses (bp : Expr) : Expr :=
    if isBuy then b2 .le bp (v "price") else b2 .le (v "price") bp
  { name := if isBuy then "gen_process_buy" else "gen_process_sell"
    params := [("id", .u64), ("account", .u64), ("side", .code), ("otype", .code),
               ("stp", .code), ("price", .u64), ("qty", .u64)]
    locals := [("rem", .u64), ("stop", .bool), ("best", .level), ("passive", .order),
               ("nextp", .order), ("victim", .order), ("fill", .u64), ("prem", .u64),
               ("ord", .order), ("lvl", .level), ("isnew", .bool), ("ok", .bool)]
    ret := .code
    entry := false
    body := Stmt.block [
      -- Post-only: the crossing decision `process` makes, before any trade.
      whenS (eqc "otype" OT_POST_ONLY) (Stmt.block [
        call1 "best" (.tBest contra) [],
        whenS (and' (not' (.isNullL (v "best"))) (crosses (.getL (v "best") .price)))
          (retc .rejectedPostOnly)]),
      .assign "rem" (v "qty"),
      -- Match against the contra side, best level first.
      .loop (.capPlus 1) (and' (b2 .lt (u 0) (v "rem")) (not' (v "stop"))) (Stmt.block [
        call1 "best" (.tBest contra) [],
        .ite (.isNullL (v "best")) (.assign "stop" (.blit true)) (
        .ite (and' (nec "otype" OT_MARKET) (not' (crosses (.getL (v "best") .price))))
          (.assign "stop" (.blit true)) (Stmt.block [
          call1 "passive" .qFirst [v "best"],
          .loop (.capPlus 1) (and' (not' (.isNullO (v "passive"))) (b2 .lt (u 0) (v "rem")))
            (.ite (and' (and' (b2 .ne (v "account") (u 0))
                              (b2 .eq (v "account") (.getO (v "passive") .account)))
                        (nec "stp" STP_NONE))
              -- Self-trade prevention, the incoming order's mode.
              (.ite (eqc "stp" STP_CANCEL_NEW) (.assign "rem" (u 0)) (
               .ite (or' (eqc "stp" STP_CANCEL_OLD) (eqc "stp" STP_CANCEL_BOTH)) (Stmt.block [
                  .assign "victim" (v "passive"),
                  call1 "passive" .qNext [v "passive"],
                  removeResting "best" "victim",
                  whenS (eqc "stp" STP_CANCEL_BOTH) (.assign "rem" (u 0))])
               -- STP_DECREMENT
               (Stmt.block [
                  .call (some "fill") "gen_min_u64" [v "rem", .getO (v "passive") .remaining],
                  .assign "rem" (b2 .sub (v "rem") (v "fill")),
                  .assign "prem" (b2 .sub (.getO (v "passive") .remaining) (v "fill")),
                  call0 (.setO .remaining) [v "passive", v "prem"],
                  call1 "nextp" .qNext [v "passive"],
                  whenS (b2 .eq (v "prem") (u 0)) (removeResting "best" "passive"),
                  .assign "passive" (v "nextp")])))
              -- A fill at the level's price.
              (Stmt.block [
                .call (some "fill") "gen_min_u64" [v "rem", .getO (v "passive") .remaining],
                .assign "rem" (b2 .sub (v "rem") (v "fill")),
                .assign "prem" (b2 .sub (.getO (v "passive") .remaining) (v "fill")),
                call0 (.setO .remaining) [v "passive", v "prem"],
                .emit (.getO (v "passive") .id) (v "id") (.getL (v "best") .price) (v "fill"),
                call1 "nextp" .qNext [v "passive"],
                whenS (b2 .eq (v "prem") (u 0)) (removeResting "best" "passive"),
                .assign "passive" (v "nextp")])),
          -- Free a level when its last order leaves.
          whenS (b2 .eq (.getL (v "best") .count) (u 0)) (Stmt.block [
            call0 (.tRemove contra) [v "best"],
            call0 .levelFree [v "best"]])]))]),
      -- Rest the remainder of a LIMIT or POST_ONLY order.
      whenS (and' (b2 .lt (u 0) (v "rem")) (and' (nec "otype" OT_IOC) (nec "otype" OT_MARKET)))
        (Stmt.block [
        call1 "ord" .orderAlloc [],
        whenS (.isNullO (v "ord")) (retc .rejectedCapacity),
        call0 (.setO .id) [v "ord", v "id"],
        call0 (.setO .account) [v "ord", v "account"],
        call0 (.setO .side) [v "ord", v "side"],
        call0 (.setO .stpMode) [v "ord", v "stp"],
        call0 (.setO .price) [v "ord", v "price"],
        call0 (.setO .qty) [v "ord", v "qty"],
        call0 (.setO .remaining) [v "ord", v "rem"],
        call1 "lvl" (.tFind own) [v "price"],
        whenS (.isNullL (v "lvl")) (Stmt.block [
          call1 "lvl" .levelAlloc [],
          whenS (.isNullL (v "lvl")) (Stmt.block [
            call0 .orderFree [v "ord"],
            retc .rejectedCapacity]),
          call0 (.setL .price) [v "lvl", v "price"],
          call0 (.tInsert own) [v "lvl"],
          .assign "isnew" (.blit true)]),
        call0 .qInsertTail [v "lvl", v "ord"],
        call1 "ok" .hashInsert [v "ord"],
        whenS (not' (v "ok")) (Stmt.block [
          call0 .qRemove [v "lvl", v "ord"],
          whenS (and' (v "isnew") (b2 .eq (.getL (v "lvl") .count) (u 0))) (Stmt.block [
            call0 (.tRemove own) [v "lvl"],
            call0 .levelFree [v "lvl"]]),
          call0 .orderFree [v "ord"],
          retc .rejectedDuplicate])]),
      retc .accepted] }

/-- `MatchingEngine_ProcessOrder`: the entry checks, in `processB`'s order. -/
def processOrderFun : FunDef where
  name := "gen_process_order"
  params := [("id", .u64), ("account", .u64), ("side", .code), ("otype", .code),
             ("stp", .code), ("price", .u64), ("qty", .u64)]
  locals := [("dup", .order), ("r", .code)]
  ret := .code
  entry := true
  body := Stmt.block [
    -- 1. Unsupported order type.
    whenS (not' (or' (or' (eqc "otype" OT_LIMIT) (eqc "otype" OT_MARKET))
                     (or' (eqc "otype" OT_IOC) (eqc "otype" OT_POST_ONLY))))
      (retc .rejectedUnsupported),
    -- 2. Invalid request.
    whenS (not' (or' (eqc "side" SIDE_BUY) (eqc "side" SIDE_SELL))) (retc .rejectedInvalid),
    whenS (not' (or' (or' (eqc "stp" STP_NONE) (eqc "stp" STP_CANCEL_NEW))
                     (or' (or' (eqc "stp" STP_CANCEL_OLD) (eqc "stp" STP_CANCEL_BOTH))
                          (eqc "stp" STP_DECREMENT))))
      (retc .rejectedInvalid),
    whenS (b2 .eq (v "qty") (u 0)) (retc .rejectedInvalid),
    whenS (and' (nec "otype" OT_MARKET) (b2 .eq (v "price") (u 0))) (retc .rejectedInvalid),
    whenS (b2 .lt qmaxE (v "qty")) (retc .rejectedInvalid),
    -- 3. Duplicate id.
    call1 "dup" .hashFind [v "id"],
    whenS (not' (.isNullO (v "dup"))) (retc .rejectedDuplicate),
    -- 4. Capacity: the request may rest and the store is full.
    whenS (and' (or' (eqc "otype" OT_LIMIT) (eqc "otype" OT_POST_ONLY))
                (b2 .le .capacity .count))
      (retc .rejectedCapacity),
    -- Dispatch on the side.
    .ite (eqc "side" SIDE_BUY)
      (.call (some "r") "gen_process_buy"
        [v "id", v "account", v "side", v "otype", v "stp", v "price", v "qty"])
      (.call (some "r") "gen_process_sell"
        [v "id", v "account", v "side", v "otype", v "stp", v "price", v "qty"]),
    .ret (v "r")]

/-- `MatchingEngine_CancelOrder`. -/
def cancelOrderFun : FunDef where
  name := "gen_cancel_order"
  params := [("id", .u64)]
  locals := [("ord", .order), ("lvl", .level), ("side", .code)]
  ret := .code
  entry := true
  body := Stmt.block [
    call1 "ord" .hashFind [v "id"],
    whenS (.isNullO (v "ord")) (retc .rejectedUnknownId),
    call1 "lvl" .owner [v "ord"],
    whenS (.isNullL (v "lvl")) (retc .rejectedUnknownId),
    -- Read the side before the order is freed.
    .assign "side" (.getO (v "ord") .side),
    removeResting "lvl" "ord",
    whenS (b2 .eq (.getL (v "lvl") .count) (u 0)) (Stmt.block [
      .ite (eqc "side" SIDE_BUY)
        (call0 (.tRemove .bids) [v "lvl"])
        (call0 (.tRemove .asks) [v "lvl"]),
      call0 .levelFree [v "lvl"]]),
    retc .cancelled]

def program : Program where
  funs := [minFun, sideFun true, sideFun false, processOrderFun, cancelOrderFun]
  tradeCap := .capPlus 1

end MatcherProgram

