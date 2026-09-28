import Matcher.Print
import Matcher.AstDump
import Bridge.EngineDbAbs

/-!
# Semantics test generator (plan v2 Phase 5, item 3)

Generates random programs in the matcher language, runs each under `execStmt`
(`runEntry`, on the model store `AbsStore cap`), prints each as C with
`Print.program`, and writes, per program `k`:

* `prog<k>.c`: the printed program; its entry is `t_main`, returning `u64`;
* `prog<k>.sexp`: its syntax tree (`AstDump.dump`), for the printer check;
* `prog<k>.exp`: the semantic outcome, `ok <value> <count> <trades…>` or
  `trap <class>` with the class `Print.trapCode` gives the error.

`tests/semantics/run.sh` compiles each program with the harness under
`gcc -O0`, `gcc -O2` and `clang -O2`, and compares exactly. Nothing is
filtered: the generator only produces programs whose errors are of a class
the C traps (overflow and division by zero, loop bound, trade buffer, missing
return), so a semantic error that is not one of these (`invalidHandle`,
`contract`, `type`, …) is printed as `leanerr` and fails the comparison.

What the programs contain: expressions with several store reads
(`capacity`, `count`, order fields) and pure arithmetic; `&&`/`||` guarding
reads through possibly-null handles; overflow-adjacent constants; loops
bounded by a literal or by `capacity + k`, with iteration counts at the bound
minus one, at the bound and above it, and with `capacity + k` overflowing;
trade emission up to and past the buffer; calls to helper functions, some of
which fall off their end.

Run: `lake env lean --run lean/Matcher/SemTest.lean <seed> <count> <cap> <outdir>`
-/

namespace SemTest

open Matcher EngineDbApi EngineDbAbs

-- ============================================================================
-- A deterministic generator
-- ============================================================================

instance : Inhabited OField := ⟨.id⟩
instance : Inhabited BinOp := ⟨.add⟩

abbrev G := StateM UInt64

def next : G Nat := do
  let x ← get
  let x' := x * 6364136223846793005 + 1442695040888963407
  set x'
  return (x' >>> 33).toNat

def pick (n : Nat) : G Nat := do return (← next) % (max n 1)

def choose {α : Type} [Inhabited α] (xs : List α) : G α := do
  return xs.getD (← pick xs.length) default

def U64MAX : Nat := 2 ^ 64 - 1

/-- Constants, weighted towards overflow edges. -/
def genLit : G UInt64 := do
  match ← pick 16 with
  | 0 => return 0
  | 1 => return 1
  | 2 => return (← choose [2, 3, 7, 10, 100])
  | 3 => return (← choose [U64MAX, U64MAX - 1, 2 ^ 63, 2 ^ 63 - 1, 2 ^ 32, 2 ^ 32 - 1]).toUInt64
  | _ => return ((← pick 20) : Nat).toUInt64

def u64Vars : List Ident := ["x0", "x1", "x2", "x3"]
def u64Fields : List OField := [.id, .account, .price, .qty, .remaining]

/-- A `u64` expression; `ord` is a handle known non-null here, if any. -/
partial def genU64 (d : Nat) (ord : Option Ident) : G Expr := do
  let leaf : G Expr := do
    match ← pick 6 with
    | 0 | 1 => return .lit (← genLit)
    | 2 | 3 => return .var (← choose u64Vars)
    | 4 => return (← choose [Expr.capacity, Expr.count])
    | _ =>
      match ord with
      | some o => return .getO (.var o) (← choose u64Fields)
      | none => return .count
  if d = 0 then leaf else
  match ← pick 7 with
  | 0 | 1 => leaf
  | _ =>
    let op ← choose [BinOp.add, .add, .add, .add, .add, .add, .sub, .mul, .div]
    return .bin op (← genU64 (d - 1) ord) (← genU64 (d - 1) ord)

partial def genBool (d : Nat) (ord : Option Ident) : G Expr := do
  match ← pick (if d = 0 then 4 else 8) with
  | 0 => return .blit ((← pick 2) = 0)
  | 1 => return .var "b0"
  | 2 | 3 => return .bin (← choose [BinOp.eq, .ne, .lt, .le]) (← genU64 1 ord) (← genU64 1 ord)
  | 4 =>
    -- a read through a handle, guarded by `&&`: short-circuit
    let o ← choose ["o0", "o1"]
    return .bin .and (.un .not (.isNullO (.var o)))
      (.bin (← choose [BinOp.lt, .le, .eq]) (.getO (.var o) (← choose u64Fields)) (← genU64 1 ord))
  | 5 => return .bin .and (← genBool (d - 1) ord) (← genBool (d - 1) ord)
  | 6 => return .bin .or (← genBool (d - 1) ord) (← genBool (d - 1) ord)
  | _ => return .un .not (← genBool (d - 1) ord)

-- ============================================================================
-- Statements
-- ============================================================================

def blk (ss : List Stmt) : Stmt := Stmt.block ss

/-- Allocate an order and, if that succeeded, set all seven fields (so every
    later read sees a value the program wrote). -/
def genAlloc (o : Ident) : G Stmt := do
  let sets : List Stmt := [
    .ext none (.setO .id) [.var o, .lit (← genLit)],
    .ext none (.setO .account) [.var o, .lit (← genLit)],
    .ext none (.setO .side) [.var o, .clit ((← pick 3).toUInt8)],
    .ext none (.setO .stpMode) [.var o, .clit ((← pick 5).toUInt8)],
    .ext none (.setO .price) [.var o, .lit (← genLit)],
    .ext none (.setO .qty) [.var o, .lit (← genLit)],
    .ext none (.setO .remaining) [.var o, .lit (← genLit)]]
  return blk [.ext (some o) .orderAlloc [], .ite (.isNullO (.var o)) .skip (blk sets)]

/-- A loop with counter `i` against `n`, bounded by `bnd`: `n` is the bound
    minus one, the bound, or above it (the bound error). -/
def genLoopHead (cap : Nat) (i : Ident) : G (Bound × Expr) := do
  match ← pick (if cap = 0 then 8 else 9) with
  | 0 | 1 | 2 | 3 =>
    let k ← pick 6
    let n ← choose [k, k + 1, k + 2, if k = 0 then 0 else k - 1]
    return (.lit k, .lit n.toUInt64)
  | 4 | 5 | 6 | 7 =>
    let k ← pick 3
    let n ← choose [Expr.bin .add .capacity (.lit k.toUInt64),
      .bin .add .capacity (.lit (k + 1).toUInt64), .capacity, .lit 0]
    return (.capPlus k, n)
  | _ =>
    -- capacity + k overflows (k = 2^64 - capacity is the first overflowing
    -- value): the loop fails before its first iteration
    let k ← choose [U64MAX, 2 ^ 64 - cap]
    return (.capPlus k, .lit 1)

mutual

partial def genStmt (cap : Nat) (d : Nat) (depth : Nat) (helpers : List Ident) : G Stmt := do
  match ← pick (if d = 0 then 5 else 12) with
  | 0 | 1 => return .assign (← choose u64Vars) (← genU64 2 none)
  | 2 => return .assign "b0" (← genBool 2 none)
  | 3 =>
    -- a read through a handle, guarded by a null test
    let o ← choose ["o0", "o1"]
    return .ite (.isNullO (.var o)) (.assign (← choose u64Vars) (← genU64 1 none))
      (.assign (← choose u64Vars) (← genU64 2 (some o)))
  | 4 =>
    if helpers.isEmpty then return .emit (← genU64 1 none) (← genU64 1 none) (← genU64 1 none) (← genU64 1 none)
    else return .call (some (← choose u64Vars)) (← choose helpers) [← genU64 1 none, ← genU64 1 none]
  | 5 => genAlloc (← choose ["o0", "o1"])
  | 6 => return .emit (← genU64 1 none) (← genU64 1 none) (← genU64 1 none) (← genU64 1 none)
  | 7 => return .ite (← genBool 2 none) (← genBlock cap (d - 1) depth helpers) (← genBlock cap (d - 1) depth helpers)
  | 8 | 10 =>
    if depth ≥ 2 then return .assign "x0" (← genU64 1 none) else
    let i := s!"i{depth}"
    let (bnd, n) ← genLoopHead cap i
    let body ← genBlock cap (d - 1) (depth + 1) helpers
    return blk [.assign i (.lit 0),
      .loop bnd (.bin .lt (.var i) n) (blk [body, .assign i (.bin .add (.var i) (.lit 1))])]
  | 9 =>
    -- emission up to and past the trade buffer (`capacity + 1` trades)
    let i := s!"i{min depth 1}"
    let k ← pick 3
    return blk [.assign i (.lit 0),
      .loop (.capPlus 3) (.bin .lt (.var i) (.bin .add .capacity (.lit k.toUInt64)))
        (blk [.emit (.var i) (.lit 1) (.lit 2) (.lit 3), .assign i (.bin .add (.var i) (.lit 1))])]
  | _ => return .ret (← genU64 2 none)

partial def genBlock (cap : Nat) (d : Nat) (depth : Nat) (helpers : List Ident) : G Stmt := do
  let n ← pick 4
  let mut ss := []
  for _ in [0:n + 1] do
    ss := ss ++ [← genStmt cap d depth helpers]
  return blk ss

end

def locals : List (Ident × Ty) :=
  [("x0", .u64), ("x1", .u64), ("x2", .u64), ("x3", .u64), ("b0", .bool), ("o0", .order),
   ("o1", .order), ("i0", .u64), ("i1", .u64)]

/-- A helper function `name(a, b)`; it may fall off its end. -/
def genHelper (cap : Nat) (name : Ident) (earlier : List Ident) : G FunDef := do
  let body ← genBlock cap 2 0 earlier
  let fin ← if (← pick 6) = 0 then pure Stmt.skip else pure (Stmt.ret (← genU64 2 none))
  return { name := name, params := [("x0", .u64), ("x1", .u64)],
           locals := locals.filter (fun p => p.1 != "x0" && p.1 != "x1"), ret := .u64,
           entry := false, body := blk [body, fin] }

def genProgram (cap : Nat) : G Program := do
  let nh ← pick 3
  let mut helpers : List FunDef := []
  let mut names : List Ident := []
  for k in [0:nh] do
    let name := s!"h{k}"
    helpers := helpers ++ [← genHelper cap name names]
    names := names ++ [name]
  let body ← genBlock cap 3 0 names
  let fin ← if (← pick 10) = 0 then pure Stmt.skip else pure (Stmt.ret (← genU64 2 none))
  let main : FunDef := { name := "t_main", params := [], locals := locals, ret := .u64,
                         entry := true, body := blk [body, fin] }
  return { funs := helpers ++ [main], tradeCap := .capPlus 1 }

-- ============================================================================
-- The semantic outcome
-- ============================================================================

def errName : Err → String
  | .type => "type" | .unbound => "unbound" | .overflow => "overflow"
  | .invalidHandle => "invalidHandle" | .contract => "contract" | .bound => "bound"
  | .tradeBuffer => "tradeBuffer" | .fuel => "fuel" | .noFun => "noFun"
  | .noReturn => "noReturn" | .arity => "arity"

def outcome (cap : Nat) (P : Program) : String :=
  match runEntry (S := AbsStore cap) P 64 "t_main" [] EngineDb.init with
  | .ok (.u64 v, s, ts) =>
    let tr := " ".intercalate (ts.map fun t => s!"{t.makerId},{t.takerId},{t.price},{t.qty}")
    s!"ok {v.toNat} {EngineDb.count s} [{tr}]"
  | .ok (_, _, _) => "leanerr type"
  | .error e =>
    let k := Matcher.Print.trapCode e
    if k = 0 then s!"leanerr {errName e}" else s!"trap {k}"

end SemTest

open SemTest in
def main (args : List String) : IO UInt32 := do
  let seed := (args.getD 0 "1").toNat!.toUInt64
  let count := (args.getD 1 "100").toNat!
  let cap := (args.getD 2 "3").toNat!
  let dir := args.getD 3 "."
  let mut x := seed * 2862933555777941757 + 3037000493 + cap.toUInt64 * 0x9E3779B97F4A7C15
  let mut classes : List (String × Nat) := []
  for k in [0:count] do
    let (P, x') := (genProgram cap).run x
    x := x'
    IO.FS.writeFile s!"{dir}/prog{k}.c" (Matcher.Print.program P)
    IO.FS.writeFile s!"{dir}/prog{k}.sexp" (AstDump.dump P)
    let o := outcome cap P
    IO.FS.writeFile s!"{dir}/prog{k}.exp" (o ++ "\n")
    let cls := (o.splitOn " ").take 2 |> " ".intercalate
    let cls := if o.startsWith "ok" then "ok" else cls
    classes := if classes.any (·.1 == cls) then classes.map fun (c, n) => if c == cls then (c, n + 1) else (c, n)
      else classes ++ [(cls, 1)]
  IO.println s!"semtest: seed {seed}, {count} programs, cap {cap}; outcomes {classes}"
  return 0
