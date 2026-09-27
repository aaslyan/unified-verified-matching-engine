import Matcher.Print
import Bridge.EngineDbAbs

/-!
# Fragment check program

A small program that uses every construct of the matcher language: every
type, every operator, every extern operation, both handle tests, internal
calls, a bounded loop, `emit` and `ret`. `main` prints it as C on stdout
(compiled by `scripts/matcher_fragment_check.sh` under gcc and clang) and runs
it under the Lean semantics on the model store, reporting on stderr.
-/

namespace Matcher.Example

open Matcher EngineDbApi EngineDbAbs

def v (x : Ident) : Expr := .var x
def u (n : UInt64) : Expr := .lit n
def b2 (op : BinOp) (a b : Expr) : Expr := .bin op a b

/-- `min` on `u64`, as an internal function. -/
def minFun : FunDef where
  name := "min_u64"
  params := [("a", .u64), ("b", .u64)]
  locals := []
  ret := .u64
  entry := false
  body := .ite (b2 .lt (v "a") (v "b")) (.ret (v "a")) (.ret (v "b"))

/-- Rest an order on the bid side, then walk its level. -/
def restFun : FunDef where
  name := "demo_rest"
  params := [("id", .u64), ("side", .code), ("price", .u64), ("qty", .u64)]
  locals := [("o", .order), ("lv", .level), ("p", .order), ("best", .level),
             ("ok", .bool), ("n", .u64), ("fill", .u64), ("rem", .u64), ("cnt", .u64)]
  ret := .code
  entry := true
  body := Stmt.block [
    .ext (some "o") .orderAlloc [],
    .ite (.isNullO (v "o")) (.ret (.clit 1)) .skip,
    .call (some "fill") "min_u64" [v "qty", u 5],
    .assign "rem" (b2 .sub (v "qty") (v "fill")),
    .ext none (.setO .id) [v "o", v "id"],
    .ext none (.setO .account) [v "o", u 7],
    .ext none (.setO .side) [v "o", v "side"],
    .ext none (.setO .stpMode) [v "o", .clit 0],
    .ext none (.setO .price) [v "o", b2 .mul (v "price") (u 1)],
    .ext none (.setO .qty) [v "o", v "qty"],
    .ext none (.setO .remaining) [v "o", b2 .add (v "rem") (v "fill")],
    .ext (some "lv") (.tFind .bids) [v "price"],
    .ite (.isNullL (v "lv"))
      (Stmt.block [
        .ext (some "lv") .levelAlloc [],
        .ite (.isNullL (v "lv"))
          (Stmt.block [.ext none .orderFree [v "o"], .ret (.clit 1)]) .skip,
        .ext none (.setL .price) [v "lv", v "price"],
        .ext none (.tInsert .bids) [v "lv"]])
      .skip,
    .ext none .qInsertTail [v "lv", v "o"],
    .ext (some "ok") .hashInsert [v "o"],
    .ite (.un .not (v "ok")) (.ret (.clit 2)) .skip,
    .ext (some "p") .qFirst [v "lv"],
    .loop 8 (.un .not (.isNullO (v "p"))) (Stmt.block [
      .assign "n" (b2 .add (v "n") (u 1)),
      .emit (.getO (v "p") .id) (v "id") (.getO (v "p") .price) (.getO (v "p") .remaining),
      .ext (some "p") .qNext [v "p"]]),
    .ext (some "best") (.tBest .bids) [],
    .ite (b2 .and (.un .not (.isNullL (v "best"))) (b2 .eq (.getO (v "o") .side) (.clit 0)))
      (.assign "cnt" (.getL (v "best") .count)) .skip,
    .ite (b2 .or (b2 .ne (v "cnt") (v "n")) (b2 .le (v "n") (u 0)))
      (.ret (.clit 3)) .skip,
    .ret (.clit 0)]

/-- Cancel by id: every removal operation. -/
def cancelFun : FunDef where
  name := "demo_cancel"
  params := [("id", .u64)]
  locals := [("o", .order), ("lv", .level), ("same", .bool)]
  ret := .code
  entry := true
  body := Stmt.block [
    .ext (some "o") .hashFind [v "id"],
    .ite (.isNullO (v "o")) (.ret (.clit 1)) .skip,
    .ext (some "lv") .owner [v "o"],
    .assign "same" (b2 .eq (v "o") .nullO),
    .ite (b2 .ne (v "lv") .nullL) .skip (.ret (.clit 1)),
    .ext none .qRemove [v "lv", v "o"],
    .ext none .hashRemove [v "o"],
    .ext none .orderFree [v "o"],
    .ite (b2 .eq (.getL (v "lv") .count) (u 0))
      (Stmt.block [.ext none (.tRemove .bids) [v "lv"], .ext none .levelFree [v "lv"]])
      .skip,
    .ret (.clit 0)]

/-- Uses the ask tree once each, so every extern prints. Never called. -/
def asksFun : FunDef where
  name := "demo_asks"
  params := [("price", .u64)]
  locals := [("lv", .level), ("o", .order), ("t", .bool)]
  ret := .bool
  entry := true
  body := Stmt.block [
    .ext (some "lv") (.tFind .asks) [v "price"],
    .ext (some "lv") (.tBest .asks) [],
    .ite (.isNullL (v "lv")) (.ret (.blit false)) .skip,
    .ext none (.tInsert .asks) [v "lv"],
    .ext none (.tRemove .asks) [v "lv"],
    .assign "o" .nullO,
    .ret (b2 .or (.blit true) (v "t"))]

/-- `x + 1`: an error in the semantics, a trap in C, when `x` is the maximum. -/
def succFun : FunDef where
  name := "demo_succ"
  params := [("x", .u64)]
  locals := []
  ret := .u64
  entry := true
  body := .ret (b2 .add (v "x") (u 1))

def program : Program where
  funs := [minFun, restFun, cancelFun, asksFun, succFun]
  tradeCap := 8

def showRun (r : Except Err (Val × AbsStore 4 × List ProcessB.TradeObs)) : String :=
  match r with
  | .ok (val, s, ts) =>
    s!"ok {repr val}, {ts.length} trade(s), live orders {s.db.oLive.length}, live levels {s.db.lLive.length}"
  | .error e => s!"error {repr e}"

def run (f : Ident) (args : List Val) (s : AbsStore 4) :=
  runEntry program 200 f args s

end Matcher.Example

open Matcher Matcher.Example in
def main : IO Unit := do
  IO.println (Print.program program)
  let s0 : EngineDbAbs.AbsStore 4 := EngineDbApi.EngineDb.init
  let r1 := run "demo_rest" [.u64 10, .code 0, .u64 100, .u64 3] s0
  IO.eprintln s!"demo_rest(10, buy, 100, 3): {showRun r1}"
  match r1 with
  | .ok (_, s1, _) =>
    let r2 := run "demo_rest" [.u64 11, .code 0, .u64 100, .u64 9] s1
    IO.eprintln s!"demo_rest(11, buy, 100, 9): {showRun r2}"
    match r2 with
    | .ok (_, s2, _) =>
      IO.eprintln s!"demo_cancel(10): {showRun (run "demo_cancel" [.u64 10] s2)}"
      IO.eprintln s!"demo_rest(10, buy, 100, 3) again (duplicate id): {showRun (run "demo_rest" [.u64 10, .code 0, .u64 100, .u64 3] s2)}"
    | .error _ => pure ()
  | .error _ => pure ()
  IO.eprintln s!"demo_succ(2^64-2): {showRun (run "demo_succ" [.u64 18446744073709551614] s0)}"
  IO.eprintln s!"demo_succ(2^64-1), overflow: {showRun (run "demo_succ" [.u64 18446744073709551615] s0)}"

