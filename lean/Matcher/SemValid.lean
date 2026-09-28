import Matcher.SemTest

/-!
# Semantics test, validity-aware (plan v2 Phase 5, extension 5b)

`SemTest` programs touch the store only through allocation, field writes and
field reads. This generator emits programs that use **every kind of store
call** — both pools (alloc/free), order and level field writes and reads,
the hash (find/insert/remove), the queues (insert-tail/remove/first/next),
`owner`, both trees (find/insert/remove/best), `capacity`, `count` — and the
null-handle test, and every handle use is valid at its point of use.

How validity is guaranteed without filtering: the generator runs the model
store (`AbsStore cap`, the store `execStmt` runs on) alongside the program it
emits. The store part of `t_main` is straight-line, so the generator knows the
store and every handle variable's value before each statement, and it emits a
store call only when that call's contract precondition holds in the model at
that point (the precondition `runExt` checks: live handles, not queued / not
hashed / not in a tree / empty queue / fresh price, as the operation requires).
A freed handle's variables are dead until reassigned, even when a later
allocation reuses the handle number (the model store reuses numbers, so the
number alone would alias the new row).
A field is read only after the program wrote it (allocated rows have
unspecified contents), and a null test or guarded read uses a handle variable
only while it is null or live. Pure statements from `SemTest` (arithmetic,
branches, bounded loops, trade emission, helper calls) are interleaved; they
use no handle.

Each program's semantic outcome is computed by `runEntry` on the model store,
exactly as in `SemTest`; the C side runs the printed program on the adapter +
handwritten data layer. `run.sh` with `GEN=semvalid` compares them.

**Validity is a permanent property of this generator, not an option.** The
contract does not fix a handle-reuse policy: which handle an allocation
returns is left to the store. The model store and the C data layer choose
differently, so a program that uses a stale handle can observe the difference,
and exact agreement between them is meaningful only for programs whose handle
uses are valid. (The refinement theorem is unaffected: it quantifies over
every store satisfying the laws.) No configuration turns the checks off.

Configurations (`SEMVALID_CFG`):
* default: pure statements from `SemTest`, with every trap edge; many
  programs trap part-way;
* `small`: longer programs (40–119 statements) whose pure statements use
  small constants and cannot trap, except one in 48 drawn from `SemTest`; about
  nine programs in ten run to completion, so long store-call sequences are
  executed to the end.

Run: `[SEMVALID_CFG=small] semvalid <seed> <count> <cap> <outdir>`
-/

namespace SemValid

open Matcher EngineDbApi EngineDbAbs SemTest

instance : Inhabited OrderRow := ⟨OrderRow.dflt⟩
instance : Inhabited LevelRow := ⟨{ price := 0 }⟩

structure VS (cap : Nat) where
  rng : UInt64
  s : AbsStore cap
  ov : Array (Option Nat)            -- o0..o3
  lv : Array (Option Nat)            -- l0..l2
  known : List (Nat × List OField)   -- fields written, per order handle
  pk : List Nat                      -- level handles whose price was written
  cov : List (String × Nat)

abbrev V (cap : Nat) := StateM (VS cap)

variable {cap : Nat}

def liftG {α : Type} (g : G α) : V cap α := do
  let st ← get
  let (a, r) := g.run st.rng
  set { st with rng := r }
  return a

def db : V cap Db := do return (← get).s.db

def addCov (cov : List (String × Nat)) (k : String) (m : Nat) : List (String × Nat) :=
  if cov.any (fun p => p.1 == k) then cov.map fun (c, n) => if c == k then (c, n + m) else (c, n)
  else cov ++ [(k, m)]

def tick (k : String) : V cap Unit :=
  modify fun st => { st with cov := addCov st.cov k 1 }

def oName (i : Nat) : Ident := s!"o{i}"
def lName (i : Nat) : Ident := s!"l{i}"
def nO : Nat := 4
def nL : Nat := 3

/-- Live handle held by variable `i`, if any. -/
def oLive (i : Nat) : V cap (Option Nat) := do
  let st ← get
  match st.ov[i]! with
  | some h => return if liveO st.s.db h then some h else none
  | none => return none

def lLive (i : Nat) : V cap (Option Nat) := do
  let st ← get
  match st.lv[i]! with
  | some l => return if liveL st.s.db l then some l else none
  | none => return none

/-- The variable is null or holds a live handle: it may be null-tested. -/
def oTestable (i : Nat) : V cap Bool := do
  let st ← get
  match st.ov[i]! with
  | none => return true
  | some h => return liveO st.s.db h

def lTestable (i : Nat) : V cap Bool := do
  let st ← get
  match st.lv[i]! with
  | none => return true
  | some l => return liveL st.s.db l

def knownOf (h : Nat) : V cap (List OField) := do
  return ((← get).known.find? (·.1 == h)).map (·.2) |>.getD []

def setKnown (h : Nat) (fs : List OField) : V cap Unit :=
  modify fun st => { st with known := (h, fs) :: st.known.filter (·.1 != h) }

def setOv (i : Nat) (v : Option Nat) : V cap Unit := modify fun st => { st with ov := st.ov.set! i v }
def setLv (i : Nat) (v : Option Nat) : V cap Unit := modify fun st => { st with lv := st.lv.set! i v }
def setS (s : AbsStore cap) : V cap Unit := modify fun st => { st with s := s }

/-- Handle number standing for a freed handle: never live, never null. -/
def staleH : Nat := 1000000000

/-- After a free, every variable that held the handle is dead until it is
    reassigned. Without this, reallocation (which reuses handle numbers) would
    make a stale variable look live again, aliasing the new row. -/
def killO (h : Nat) : V cap Unit :=
  modify fun st => { st with ov := st.ov.map fun v => if v == some h then some staleH else v }
def killL (l : Nat) : V cap Unit :=
  modify fun st => { st with lv := st.lv.map fun v => if v == some l then some staleH else v }

/-- Indices `0..n-1` for which `p` holds. -/
def idxs (n : Nat) (p : Nat → V cap Bool) : V cap (List Nat) := do
  let mut r := []
  for i in [0:n] do
    if ← p i then r := r ++ [i]
  return r

def pickOf {α : Type} [Inhabited α] (xs : List α) : V cap (Option α) := do
  if xs.isEmpty then return none else return some (← liftG (choose xs))

def bump (x : Ident) (e : Expr) : Stmt := .assign x (.bin .add (.var x) e)

def treeOf (b : Bool) : Tree := if b then .bids else .asks

/-- One store statement whose contract precondition holds now, with the model
    updated as `runExt` will update the store; `none` if the chosen kind has
    no valid instance now (the caller draws again). -/
def genStoreOp : V cap (Option Stmt) := do
  let k ← liftG (pick 28)
  let d ← db
  match k with
  | 0 | 1 =>
    let i ← liftG (pick nO)
    let r := EngineDb.orderAlloc (← get).s
    setS r.2; setOv i r.1
    match r.1 with
    | some h => setKnown h []
    | none => pure ()
    tick "order_alloc"; return some (.ext (some (oName i)) .orderAlloc [])
  | 2 =>
    let i ← liftG (pick nL)
    let r := EngineDb.levelAlloc (← get).s
    setS r.2; setLv i r.1
    match r.1 with
    | some l => modify fun st => { st with pk := st.pk.filter (· != l) }
    | none => pure ()
    tick "level_alloc"; return some (.ext (some (lName i)) .levelAlloc [])
  | 3 =>
    -- order_free: live, not queued, not hashed
    let c ← idxs nO fun i => do
      match ← oLive i with
      | some h => return !(queuedB d h) && !(inHashB d h)
      | none => return false
    let some i ← pickOf c | return none
    let h := ((← oLive i)).get!
    setS (EngineDb.orderFree (← get).s h); killO h
    tick "order_free"; return some (.ext none .orderFree [.var (oName i)])
  | 4 =>
    -- level_free: live, in no tree, empty queue
    let c ← idxs nL fun i => do
      match ← lLive i with
      | some l => return !(inAnyTreeB d l) && (d.queue l).isEmpty
      | none => return false
    let some i ← pickOf c | return none
    let l := ((← lLive i)).get!
    setS (EngineDb.levelFree (← get).s l); killL l
    tick "level_free"; return some (.ext none .levelFree [.var (lName i)])
  | 5 | 6 =>
    -- set an order field (the id only while not hashed)
    let c ← idxs nO fun i => do return (← oLive i).isSome
    let some i ← pickOf c | return none
    let h := ((← oLive i)).get!
    let f ← liftG (choose [OField.id, .account, .side, .stpMode, .price, .qty, .remaining])
    let f := if f == .id && inHashB d h then OField.remaining else f
    let v : Val ← match f with
      | .side => do pure (.code ((← liftG (pick 3)).toUInt8))
      | .stpMode => do pure (.code ((← liftG (pick 5)).toUInt8))
      | .id => do pure (.u64 ((← liftG (pick 6)) + 1).toUInt64)
      | .price => do pure (.u64 ((← liftG (pick 12)) + 95).toUInt64)
      | _ => do pure (.u64 ((← liftG (pick 20)) + 1).toUInt64)
    let row := (EngineDb.readOrder (← get).s h).get!
    match setOField row f v with
    | .ok row' =>
      setS (EngineDb.writeOrder (← get).s h row')
      setKnown h (f :: (← knownOf h))
    | .error _ => pure ()
    let e : Expr := match v with | .code c => .clit c | .u64 n => .lit n | _ => .lit 0
    tick s!"order_set_{AstDump.ofield f}"
    return some (.ext none (.setO f) [.var (oName i), e])
  | 7 =>
    -- set a level's price: live, in no tree
    let c ← idxs nL fun i => do
      match ← lLive i with
      | some l => return !(inAnyTreeB d l)
      | none => return false
    let some i ← pickOf c | return none
    let l := ((← lLive i)).get!
    let p := ((← liftG (pick 12)) + 95).toUInt64
    let row := (EngineDb.readLevel (← get).s l).get!
    setS (EngineDb.writeLevel (← get).s l { row with price := p })
    modify fun st => { st with pk := l :: st.pk }
    tick "level_set_price"; return some (.ext none (.setL .price) [.var (lName i), .lit p])
  | 8 =>
    let j ← liftG (pick nO)
    let id := ((← liftG (pick 7)) + 1).toUInt64
    setOv j (EngineDb.hashFind (← get).s id)
    tick "hash_find"; return some (.ext (some (oName j)) .hashFind [.lit id])
  | 9 | 22 | 23 =>
    -- hash_insert: live, not hashed, id written
    let c ← idxs nO fun i => do
      match ← oLive i with
      | some h => return !(inHashB d h) && (← knownOf h).contains .id
      | none => return false
    let some i ← pickOf c | return none
    let h := ((← oLive i)).get!
    let r := EngineDb.hashInsert (← get).s h
    setS r.2
    tick "hash_insert"
    return some (blk [.ext (some "b0") .hashInsert [.var (oName i)], .ite (.var "b0") (bump "x3" (.lit 1)) .skip])
  | 10 =>
    let c ← idxs nO fun i => do
      match ← oLive i with
      | some h => return inHashB d h
      | none => return false
    let some i ← pickOf c | return none
    let h := ((← oLive i)).get!
    setS (EngineDb.hashRemove (← get).s h)
    tick "hash_remove"; return some (.ext none .hashRemove [.var (oName i)])
  | 11 | 12 =>
    -- queue_insert_tail: live level; live, unqueued order
    let cl ← idxs nL fun i => do return (← lLive i).isSome
    let co ← idxs nO fun i => do
      match ← oLive i with
      | some h => return !(queuedB d h)
      | none => return false
    let some i ← pickOf cl | return none
    let some j ← pickOf co | return none
    let l := ((← lLive i)).get!
    let h := ((← oLive j)).get!
    setS (EngineDb.qInsertTail (← get).s l h)
    tick "queue_insert_tail"; return some (.ext none .qInsertTail [.var (lName i), .var (oName j)])
  | 13 =>
    -- queue_remove: an order in the queue of a level some variable holds
    let mut cands : List (Nat × Nat) := []
    for i in [0:nL] do
      if let some l ← lLive i then
        for j in [0:nO] do
          if let some h ← oLive j then
            if (d.queue l).contains h then cands := cands ++ [(i, j)]
    let some (i, j) ← pickOf cands | return none
    let l := ((← lLive i)).get!
    let h := ((← oLive j)).get!
    setS (EngineDb.qRemove (← get).s l h)
    tick "queue_remove"; return some (.ext none .qRemove [.var (lName i), .var (oName j)])
  | 14 =>
    let cl ← idxs nL fun i => do return (← lLive i).isSome
    let some i ← pickOf cl | return none
    let j ← liftG (pick nO)
    let l := ((← lLive i)).get!
    setOv j (EngineDb.qFirst (← get).s l)
    tick "queue_first"; return some (.ext (some (oName j)) .qFirst [.var (lName i)])
  | 15 =>
    let co ← idxs nO fun i => do
      match ← oLive i with
      | some h => return queuedB d h
      | none => return false
    let some i ← pickOf co | return none
    let j ← liftG (pick nO)
    let h := ((← oLive i)).get!
    setOv j (EngineDb.qNext (← get).s h)
    tick "queue_next"; return some (.ext (some (oName j)) .qNext [.var (oName i)])
  | 16 =>
    let co ← idxs nO fun i => do return (← oLive i).isSome
    let some i ← pickOf co | return none
    let j ← liftG (pick nL)
    let h := ((← oLive i)).get!
    setLv j (EngineDb.owner (← get).s h)
    tick "order_owner"; return some (.ext (some (lName j)) .owner [.var (oName i)])
  | 17 =>
    let t := treeOf ((← liftG (pick 2)) = 0)
    let j ← liftG (pick nL)
    let p := ((← liftG (pick 12)) + 95).toUInt64
    setLv j (EngineDb.tFind (← get).s t p)
    tick s!"{AstDump.treeName t}_find"; return some (.ext (some (lName j)) (.tFind t) [.lit p])
  | 18 | 24 =>
    -- tree insert: live, priced, in no tree, price fresh in the tree
    let t := treeOf ((← liftG (pick 2)) = 0)
    let pk := (← get).pk
    let c ← idxs nL fun i => do
      match ← lLive i with
      | some l => return pk.contains l && !(inAnyTreeB d l) && priceFreshB d t l
      | none => return false
    let some i ← pickOf c | return none
    let l := ((← lLive i)).get!
    setS (EngineDb.tInsert (← get).s t l)
    tick s!"{AstDump.treeName t}_insert"; return some (.ext none (.tInsert t) [.var (lName i)])
  | 19 | 25 =>
    let t := treeOf ((← liftG (pick 2)) = 0)
    let c ← idxs nL fun i => do
      match ← lLive i with
      | some l => return inTreeB d t l
      | none => return false
    let some i ← pickOf c | return none
    let l := ((← lLive i)).get!
    setS (EngineDb.tRemove (← get).s t l)
    tick s!"{AstDump.treeName t}_remove"; return some (.ext none (.tRemove t) [.var (lName i)])
  | 20 =>
    let t := treeOf ((← liftG (pick 2)) = 0)
    let j ← liftG (pick nL)
    setLv j (EngineDb.tBest (← get).s t)
    tick s!"{AstDump.treeName t}_best"; return some (.ext (some (lName j)) (.tBest t) [])
  | _ =>
    -- reads: an order field written before, a level's price or count, a null
    -- test, or a read guarded by a null test with `&&`
    let x ← liftG (choose u64Vars)
    match ← liftG (pick 5) with
    | 0 =>
      let co ← idxs nO fun i => do
        match ← oLive i with
        | some h => return !((← knownOf h).filter (fun f => u64Fields.contains f)).isEmpty
        | none => return false
      let some i ← pickOf co | return none
      let h := ((← oLive i)).get!
      let f ← liftG (choose ((← knownOf h).filter fun f => u64Fields.contains f))
      tick "read_order_field"; return some (bump x (.getO (.var (oName i)) f))
    | 1 =>
      let pk := (← get).pk
      let cl ← idxs nL fun i => do return (← lLive i).isSome
      let some i ← pickOf cl | return none
      let l := ((← lLive i)).get!
      if pk.contains l && (← liftG (pick 2)) = 0 then
        tick "read_level_price"; return some (bump x (.getL (.var (lName i)) .price))
      else
        tick "read_level_count"; return some (bump x (.getL (.var (lName i)) .count))
    | 2 =>
      let co ← idxs nO oTestable
      let some i ← pickOf co | return none
      tick "null_test_order"
      return some (.ite (.isNullO (.var (oName i))) (bump x (.lit 1)) (bump x (.lit 2)))
    | 3 =>
      let cl ← idxs nL lTestable
      let some i ← pickOf cl | return none
      tick "null_test_level"
      return some (.ite (.isNullL (.var (lName i))) (bump x (.lit 1)) (bump x (.lit 2)))
    | _ =>
      -- `&&` guards a read through a handle that is null or has the field written
      let co ← idxs nO fun i => do
        let st ← get
        match st.ov[i]! with
        | none => return true
        | some h => return liveO st.s.db h && (← knownOf h).contains .qty
      let some i ← pickOf co | return none
      tick "guarded_read"
      return some (.ite (.bin .and (.un .not (.isNullO (.var (oName i))))
          (.bin .lt (.getO (.var (oName i)) .qty) (.lit 10))) (bump x (.lit 1)) .skip)

-- ============================================================================
-- The small-constants configuration
-- ============================================================================

/-! Pure statements for the `small` configuration: small literals, `+` and
division by a nonzero literal only, loops that stay within their bound,
helpers that always return, and no trade emission. None of them can trap, so
programs run to completion unless one of the rare statements drawn from the
full `SemTest` generator (with its overflow, loop-bound, trade-buffer and
missing-return edges) traps. The store part is the same as in the default
configuration, and so is the validity of every handle use. -/

partial def smallU64 (d : Nat) : G Expr := do
  let leaf : G Expr := do
    match ← pick 6 with
    | 0 | 1 => return .lit ((← pick 20).toUInt64)
    | 2 | 3 => return .var (← choose u64Vars)
    | 4 => return .capacity
    | _ => return .count
  if d = 0 then leaf else
  match ← pick 8 with
  | 0 | 1 => leaf
  | 2 => return .bin .div (← smallU64 (d - 1)) (.lit ((← pick 5) + 1).toUInt64)
  | 3 => return .bin .mul (.lit ((← pick 4).toUInt64)) (.lit ((← pick 4).toUInt64))
  | _ => return .bin .add (← smallU64 (d - 1)) (← smallU64 (d - 1))

partial def smallBool (d : Nat) : G Expr := do
  match ← pick (if d = 0 then 4 else 7) with
  | 0 => return .blit ((← pick 2) = 0)
  | 1 => return .var "b0"
  | 2 | 3 => return .bin (← choose [BinOp.eq, .ne, .lt, .le]) (← smallU64 1) (← smallU64 1)
  | 4 => return .bin .and (← smallBool (d - 1)) (← smallBool (d - 1))
  | 5 => return .bin .or (← smallBool (d - 1)) (← smallBool (d - 1))
  | _ => return .un .not (← smallBool (d - 1))

mutual

partial def smallStmt (d depth : Nat) (helpers : List Ident) : G Stmt := do
  match ← pick (if d = 0 then 4 else 7) with
  | 0 | 1 => return .assign (← choose u64Vars) (← smallU64 2)
  | 2 => return .assign "b0" (← smallBool 2)
  | 3 =>
    if helpers.isEmpty then return .assign (← choose u64Vars) (← smallU64 2)
    else return .call (some (← choose u64Vars)) (← choose helpers) [← smallU64 1, ← smallU64 1]
  | 4 => return .ite (← smallBool 2) (← smallBlock (d - 1) depth helpers) (← smallBlock (d - 1) depth helpers)
  | _ =>
    if depth ≥ 2 then return .assign "x0" (← smallU64 1) else
    let i := s!"i{depth}"
    -- iteration count at or below the bound
    let (bnd, n) ← match ← pick 2 with
      | 0 => do
        let k ← pick 6
        pure (Bound.lit k, Expr.lit (← choose [k, k - 1]).toUInt64)
      | _ => do
        let k ← pick 3
        pure (Bound.capPlus k, ← choose [Expr.bin .add .capacity (.lit k.toUInt64), .capacity, .lit 0])
    let body ← smallBlock (d - 1) (depth + 1) helpers
    return blk [.assign i (.lit 0),
      .loop bnd (.bin .lt (.var i) n) (blk [body, .assign i (.bin .add (.var i) (.lit 1))])]

partial def smallBlock (d depth : Nat) (helpers : List Ident) : G Stmt := do
  let n ← pick 3
  let mut ss := []
  for _ in [0:n + 1] do
    ss := ss ++ [← smallStmt d depth helpers]
  return blk ss

end

/-- A helper `name(a, b)` that always returns. -/
def smallHelper (name : Ident) (earlier : List Ident) : G FunDef := do
  let body ← smallBlock 2 0 earlier
  return { name := name, params := [("x0", .u64), ("x1", .u64)],
           locals := SemTest.locals.filter (fun p => p.1 != "x0" && p.1 != "x1"), ret := .u64,
           entry := false, body := blk [body, .ret (← smallU64 2)] }

def vlocals : List (Ident × Ty) :=
  [("x0", .u64), ("x1", .u64), ("x2", .u64), ("x3", .u64), ("b0", .bool), ("i0", .u64), ("i1", .u64)] ++
  (List.range nO).map (fun i => (oName i, Ty.order)) ++ (List.range nL).map (fun i => (lName i, Ty.level))

/-- `small`: the small-constants configuration (longer programs, pure
    statements that cannot trap except a rare full-generator statement). -/
def genValidProgram (cap : Nat) (small : Bool) : V cap Program := do
  let nh ← liftG (pick 2)
  let mut helpers : List FunDef := []
  let mut names : List Ident := []
  for k in [0:nh] do
    let name := s!"h{k}"
    helpers := helpers ++ [← liftG (if small then smallHelper name names else genHelper true cap name names)]
    names := names ++ [name]
  let n ← liftG (if small then do pure (40 + (← pick 80)) else do pure (15 + (← pick 40)))
  let mut ss : List Stmt := []
  let mut tries := 0
  while ss.length < n && tries < 20 * n do
    tries := tries + 1
    if (← liftG (pick (if small then 8 else 16))) = 0 then
      let full : Bool ← if small then do pure (decide ((← liftG (pick 48)) = 0)) else pure true
      ss := ss ++ [← liftG (if full then genStmt true cap 1 0 names else smallStmt 1 0 names)]
    else
      if let some st ← genStoreOp then ss := ss ++ [st]
  let fin := Stmt.ret (.bin .add (.var "x0") (.bin .add (.var "x1") (.bin .add (.var "x2") (.var "x3"))))
  let main : FunDef := { name := "t_main", params := [], locals := vlocals, ret := .u64,
                         entry := true, body := blk (ss ++ [fin]) }
  return { funs := helpers ++ [main], tradeCap := .capPlus 1 }

end SemValid

open SemValid SemTest in
def main (args : List String) : IO UInt32 := do
  let seed := (args.getD 0 "1").toNat!.toUInt64
  let count := (args.getD 1 "100").toNat!
  let cap := (args.getD 2 "3").toNat!
  let dir := args.getD 3 "."
  let small := (← IO.getEnv "SEMVALID_CFG") == some "small"
  let cfg := if small then "small" else "default"
  let mut x := seed * 2862933555777941757 + 3037000493 + cap.toUInt64 * 0x9E3779B97F4A7C15 +
    (if small then 0xD1B54A32D192ED03 else 0)
  let mut classes : List (String × Nat) := []
  let mut cov : List (String × Nat) := []
  let mut covOk : List (String × Nat) := []
  let mut nOk := 0
  for k in [0:count] do
    let st0 : VS cap := { rng := x, s := EngineDbApi.EngineDb.init, ov := Array.replicate nO none,
                          lv := Array.replicate nL none, known := [], pk := [], cov := [] }
    let (P, st) := (genValidProgram cap small).run st0
    x := st.rng
    for (c, n) in st.cov do
      cov := addCov cov c n
    IO.FS.writeFile s!"{dir}/prog{k}.c" (Matcher.Print.program P)
    IO.FS.writeFile s!"{dir}/prog{k}.sexp" (AstDump.dump P)
    let o := outcome cap P 1024
    IO.FS.writeFile s!"{dir}/prog{k}.exp" (o ++ "\n")
    if o.startsWith "ok" then
      nOk := nOk + 1
      for (c, n) in st.cov do
        covOk := addCov covOk c n
    let cls := if o.startsWith "ok" then "ok" else ((o.splitOn " ").take 2 |> " ".intercalate)
    classes := if classes.any (·.1 == cls) then classes.map fun (c, n) => if c == cls then (c, n + 1) else (c, n)
      else classes ++ [(cls, 1)]
  IO.println s!"semvalid [{cfg}]: seed {seed}, {count} programs, cap {cap}; outcomes {classes}"
  IO.println s!"semvalid coverage (store calls and handle uses emitted): {cov}"
  IO.println s!"semvalid coverage in the {nOk} programs that ran to completion (all executed): {covOk}"
  return 0
