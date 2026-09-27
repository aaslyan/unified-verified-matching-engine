import Matcher.Program
import Bridge.EngineDbAbs

/-!
# Lean-side differential check of the port

Runs the matcher program under the Lean semantics, on the model store, side
by side with the spec step `processB`, on seeded random request streams, and
compares the observation of plan v2 §4: result code, trades in order, and the
book restricted to the fields C stores. Evidence for Phase 3, not a proof;
Phase 4 proves the same equality for every request.

Run: `lake env lean --run lean/Matcher/CheckLean.lean [seed] [streams] [length] [cap]`
-/

namespace MatcherCheck

open Matcher MatcherProgram EngineDbApi EngineDbAbs ProcessB

/-- A 64-bit linear congruential generator. -/
def next (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

def pick (x : UInt64) (n : Nat) : Nat := (x >>> 33).toNat % n

/-- A random request. Ids are mostly fresh, sometimes reused (duplicates,
    cancels of live or dead orders). -/
def genReq (x : UInt64) (nextId : Nat) : Req × UInt64 × Nat :=
  let x1 := next x; let x2 := next x1; let x3 := next x2; let x4 := next x3
  let x5 := next x4; let x6 := next x5; let x7 := next x6; let x8 := next x7
  let isCancel := pick x1 10 < 2
  let reuse := pick x2 10 < 2
  let id := if reuse && nextId > 1 then 1 + pick x3 (nextId - 1) else nextId
  let nid := if reuse then nextId else nextId + 1
  if isCancel then (.cancel id.toUInt64, x8, nid)
  else
    let otRoll := pick x4 20
    let ot : Nat := if otRoll < 9 then 0 else if otRoll < 12 then 1 else if otRoll < 15 then 2
      else if otRoll < 19 then 3 else 5
    let stpRoll := pick x5 12
    let stp : Nat := if stpRoll < 6 then 0 else if stpRoll < 11 then 1 + pick x6 4 else 7
    let price := if pick x7 30 = 0 then 0 else 95 + pick x6 11
    let qty := if pick x8 40 = 0 then 0 else 1 + pick x7 9
    let r : CRequest :=
      { id := id.toUInt64, account := (pick x3 3).toUInt64,
        side := (pick x5 2).toUInt8, orderType := ot.toUInt8, stpMode := stp.toUInt8,
        price := price.toUInt64, qty := qty.toUInt64 }
    (.order r, x8, nid)

def fuel : Nat := 64

/-- One matcher step on the model store. -/
def matcherStep {cap : Nat} (s : AbsStore cap) :
    Req → Except Err (Val × AbsStore cap × List TradeObs)
  | .order r => runEntry program fuel "gen_process_order"
      [.u64 r.id, .u64 r.account, .code r.side, .code r.orderType, .code r.stpMode,
       .u64 r.price, .u64 r.qty] s
  | .cancel id => runEntry program fuel "gen_cancel_order" [.u64 id] s

structure Tally where
  steps : Nat := 0
  mismatches : Nat := 0
  codes : List (UInt8 × Nat) := []
  firstFailure : Option String := none

def bump (l : List (UInt8 × Nat)) (k : UInt8) : List (UInt8 × Nat) :=
  if l.any (·.1 == k) then l.map fun (a, n) => if a == k then (a, n + 1) else (a, n)
  else l ++ [(k, 1)]

def runStream (cap : Nat) (seed : UInt64) (len : Nat) (t : Tally) : Tally := Id.run do
  let mut s : AbsStore cap := EngineDb.init
  let mut b : BookState := BookState.empty
  let mut x := seed
  let mut nid := 1
  let mut t := t
  for i in [0:len] do
    let (req, x', nid') := genReq x nid
    x := x'; nid := nid'
    let spec := processB cap b req
    let want := obsSpec spec
    match matcherStep s req with
    | .error e =>
      t := { t with steps := t.steps + 1, mismatches := t.mismatches + 1,
                    firstFailure := t.firstFailure.orElse fun _ =>
                      some s!"seed {seed} step {i}: matcher error {repr e} on {repr req}" }
      return t
    | .ok (val, s', trades) =>
      let code := match val with | .code k => k | _ => 255
      let got : Obs := { code := want.code, trades := trades, book := bookView (absBook s'.db) }
      let ok := code == codeOf want.code && got.trades == want.trades && got.book == want.book
      t := { t with steps := t.steps + 1, codes := bump t.codes code,
                    mismatches := if ok then t.mismatches else t.mismatches + 1,
                    firstFailure := if ok then t.firstFailure else t.firstFailure.orElse fun _ =>
                      some s!"seed {seed} step {i}: {repr req}: code {code} vs {codeOf want.code}, trades {repr trades} vs {repr want.trades}" }
      if !ok then return t
      s := s'; b := spec.2.book
  return t

end MatcherCheck

open MatcherCheck in
def main (args : List String) : IO UInt32 := do
  let seed := (args.getD 0 "1").toNat!.toUInt64
  let streams := (args.getD 1 "200").toNat!
  let len := (args.getD 2 "60").toNat!
  let cap := (args.getD 3 "6").toNat!
  let mut t : Tally := {}
  for k in [0:streams] do
    t := runStream cap (seed * 1000003 + k.toUInt64) len t
  IO.println s!"lean differential: {t.steps} steps, {streams} streams, cap {cap}, {t.mismatches} mismatches"
  IO.println s!"result codes seen (code, count): {t.codes}"
  match t.firstFailure with
  | some f => IO.println s!"first failure: {f}"; return 1
  | none => return 0
