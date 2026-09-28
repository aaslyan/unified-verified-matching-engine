import Walk.Spec
import Matcher.CheckLean

/-!
# Differentials for the walking spec (A1)

Three chains are stepped side by side on the same request stream, each
feeding its own output state to its next step:

* `processB` on a `BookState` (the spec of record),
* `Walk.process` on a `BookState`,
* the matcher program under `execStmt` on the model store (`MatcherCheck.matcherStep`).

**D1** compares `Walk.process` with `processB` on `obsSpec`.
**D2** compares the matcher with `Walk.process`: result code, trades
(`tradeObs`), and the book view of the decoded store.

A walk step that returns `none` (a trap) counts as a mismatch in both.

Streams: `MatcherCheck.genReq` (the Phase 3 generator, unchanged) and
`genFill` below, which rests mostly non-crossing LIMIT orders, so the book
reaches capacity and the pessimistic capacity reject is exercised.

`MatcherCheck` defines `main`, so this module cannot; `lean/Walk/CheckRun.lean`
runs `Walk.Check.runIO` under `#eval`, parameters from the environment.
-/

namespace Walk.Check

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB MatcherCheck

/-- Fill runs: 5% cancels; 70% LIMIT, 10% each POST_ONLY, IOC, MARKET;
    three quarters of the prices on the order's own side of 100 (resting),
    one quarter crossing. -/
def genFill (x : UInt64) (nextId : Nat) : Req × UInt64 × Nat :=
  let x1 := next x; let x2 := next x1; let x3 := next x2; let x4 := next x3
  let x5 := next x4; let x6 := next x5; let x7 := next x6; let x8 := next x7
  let isCancel := pick x1 20 = 0
  let id := if isCancel && nextId > 1 then 1 + pick x3 (nextId - 1) else nextId
  if isCancel then (.cancel id.toUInt64, x8, nextId)
  else
    let otRoll := pick x4 10
    let ot : Nat := if otRoll < 7 then 0 else if otRoll < 8 then 3 else if otRoll < 9 then 2 else 1
    let side := pick x5 2
    let resting := pick x2 4 != 0
    let off := pick x6 5
    -- buys rest at 95..99, sells at 101..105
    let price := if (side == 0) == resting then 95 + off else 101 + off
    let r : CRequest :=
      { id := id.toUInt64, account := (pick x3 3).toUInt64,
        side := side.toUInt8, orderType := ot.toUInt8, stpMode := (pick x7 5).toUInt8,
        price := price.toUInt64, qty := (1 + pick x8 9).toUInt64 }
    (.order r, x8, nextId + 1)

structure Tally where
  steps : Nat := 0
  d1 : Nat := 0
  d2 : Nat := 0
  traps : Nat := 0
  /-- capacity rejects of a marketable request: the pessimistic reject -/
  pessimistic : Nat := 0
  codes : List (UInt8 × Nat) := []
  first : Option String := none

def fail (t : Tally) (msg : String) : Tally :=
  { t with first := t.first.orElse fun _ => some msg }

def runStream (gen : UInt64 → Nat → Req × UInt64 × Nat) (cap : Nat) (seed : UInt64)
    (len : Nat) (t : Tally) : Tally := Id.run do
  let mut s : AbsStore cap := EngineDb.init
  let mut bS : BookState := BookState.empty
  let mut bW : BookState := BookState.empty
  let mut x := seed
  let mut nid := 1
  let mut t := t
  for i in [0:len] do
    let (req, x', nid') := gen x nid
    x := x'; nid := nid'
    let spec := processB cap bS req
    let where_ := s!"cap {cap} seed {seed} step {i}: {repr req}"
    match Walk.process cap bW req with
    | none =>
      return fail { t with steps := t.steps + 1, traps := t.traps + 1 } s!"{where_}: walk traps"
    | some w =>
      let code := codeOf w.1
      t := { t with steps := t.steps + 1, codes := bump t.codes code }
      if let .order r := req then
        let c : Ctx := { cap := cap, r := r, isBuy := r.side = 0 }
        let marketable := match tBest bW c.contra with
          | some l => r.orderType = 1 || c.crosses l.price
          | none => false
        if w.1 == .rejectedCapacity && marketable then
          t := { t with pessimistic := t.pessimistic + 1 }
      -- D1: the walk against processB
      let (o1, o2) := (obsSpec w, obsSpec spec)
      let ok1 := decide (o1.code = o2.code) && o1.trades == o2.trades && o1.book == o2.book
      if !ok1 then
        t := fail { t with d1 := t.d1 + 1 }
          s!"D1 {where_}: walk {repr (obsSpec w).code} {repr (obsSpec w).trades} vs processB {repr (obsSpec spec).code} {repr (obsSpec spec).trades}"
      -- D2: the matcher against the walk
      match matcherStep s req with
      | .error e =>
        return fail { t with d2 := t.d2 + 1 } s!"D2 {where_}: matcher error {repr e}"
      | .ok (val, s', trades) =>
        let mcode := match val with | .code k => k | _ => 255
        let ok2 := mcode == code && trades == w.2.trades.map tradeObs &&
          bookView (absBook s'.db) == bookView w.2.book
        if !ok2 then
          t := fail { t with d2 := t.d2 + 1 }
            s!"D2 {where_}: matcher {mcode} {repr trades} vs walk {code} {repr (w.2.trades.map tradeObs)}"
        if !(ok1 && ok2) then return t
        s := s'
      bS := spec.2.book; bW := w.2.book
  return t

def getNat (k : String) (d : Nat) : IO Nat := do
  return ((← IO.getEnv k).bind String.toNat?).getD d

/-- Parameters: `WALK_GEN` (`rand` or `fill`), `WALK_SEED`, `WALK_STREAMS`,
    `WALK_LEN`, `WALK_CAP`. Stream `k` is seeded `seed * 1000003 + k`, as in
    `MatcherCheck`. Fails if any mismatch or trap. -/
def runIO : IO Unit := do
  let genName := (← IO.getEnv "WALK_GEN").getD "rand"
  let gen := if genName == "fill" then genFill else genReq
  let seed := (← getNat "WALK_SEED" 7).toUInt64
  let streams ← getNat "WALK_STREAMS" 400
  let len ← getNat "WALK_LEN" 60
  let cap ← getNat "WALK_CAP" 6
  let mut t : Tally := {}
  for k in [0:streams] do
    t := runStream gen cap (seed * 1000003 + k.toUInt64) len t
  IO.println s!"walk differential [{genName}] seed {seed}, {streams} streams x {len}, cap {cap}: {t.steps} steps; D1 (walk vs processB) {t.d1} mismatches; D2 (matcher vs walk) {t.d2} mismatches; {t.traps} traps; {t.pessimistic} pessimistic capacity rejects"
  IO.println s!"  result codes (code, count): {t.codes}"
  match t.first with
  | some f => throw (IO.userError s!"first failure: {f}")
  | none => pure ()

end Walk.Check
