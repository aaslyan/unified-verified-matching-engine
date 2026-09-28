import Bridge.ProcessB
import Matcher.Program

/-!
# The executable spec as a differential oracle (plan v2 Phase 5, item 2)

Reads a request stream and runs `processB cap` from the empty book, printing
after each request the observation `Obs` the refinement theorem compares:

```
<step> code <result code, as codeOf>
  trade <maker> <taker> <price> <qty>          (one line per trade)
  bid <price> : <id>/<remaining>/<qty>/<account>/<policy> ...   (best first)
  ask <price> : ...
```

`account` is the order's STP group (0 for none, as C stores account 0) and
`policy` the STP policy code (0 for none). Stream format, one request per line:
`O <id> <account> <side> <type> <stp> <price> <qty>` or `C <id>`.

Run: `lake env lean --run lean/Matcher/Oracle.lean <cap> <stream-file>`
-/

namespace Oracle

open EngineDbApi EngineDbAbs ProcessB

def parseReq (l : String) : Option Req :=
  match (l.splitOn " ").filter (· ≠ "") with
  | ["O", i, a, s, t, m, p, q] =>
    some (.order { id := i.toNat!.toUInt64, account := a.toNat!.toUInt64, side := s.toNat!.toUInt8,
                   orderType := t.toNat!.toUInt8, stpMode := m.toNat!.toUInt8,
                   price := p.toNat!.toUInt64, qty := q.toNat!.toUInt64 })
  | ["C", i] => some (.cancel i.toNat!.toUInt64)
  | _ => none

def policyCode : Option STPPolicy → Nat
  | none => 0
  | some .cancelNewest => 1
  | some .cancelOldest => 2
  | some .cancelBoth => 3
  | some .decrement => 4

def orderStr (o : OrderView) : String :=
  s!"{o.id}/{o.remainingQty}/{o.qty}/{o.stpGroup.getD 0}/{policyCode o.stpPolicy}"

def levelStr (tag : String) (l : LevelView) : String :=
  s!"  {tag} {l.price} :" ++ String.join (l.orders.map fun o => " " ++ orderStr o)

def obsStr (k : Nat) (x : ResultCode × ProcessResult) : String :=
  let v := bookView x.2.book
  let head := s!"{k} code {(MatcherProgram.codeOf x.1).toNat}"
  let trades := x.2.trades.map fun t => s!"  trade {t.passiveId} {t.aggressorId} {t.price} {t.qty}"
  let bids := v.bids.map (levelStr "bid")
  let asks := v.asks.map (levelStr "ask")
  "\n".intercalate ([head] ++ trades ++ bids ++ asks)

end Oracle

open Oracle in
def main (args : List String) : IO UInt32 := do
  let cap := (args.getD 0 "8").toNat!
  let lines ← IO.FS.lines (args.getD 1 "/dev/stdin")
  let mut b : BookState := BookState.empty
  let out ← IO.getStdout
  let mut k := 0
  for l in lines do
    match parseReq l with
    | none => pure ()
    | some q =>
      let x := ProcessB.processB cap b q
      out.putStrLn (obsStr k x)
      b := x.2.book
      k := k + 1
  return 0
