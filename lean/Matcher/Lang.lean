import Bridge.EngineDbApi
import Bridge.ProcessB

/-!
# The matcher language

A small, memory-free imperative language for the generated matching logic
(plan v2, Phase 2, Decision 2). It has no arrays, pointers or address-of:
every access to storage goes through an extern call into the EngineDb
contract, or through a payload read/write on an opaque handle. Memory
freedom is a property of the syntax, not a side condition.

**Types.** One integer type, `u64`, for ids, prices, quantities, counts and
capacity. Enumerations (side, order type, STP mode, result code) have their
own type `code`, which supports equality only: no arithmetic, so no overflow
obligation. Plus `bool` and two opaque handle types (`order`, `level`), each
with a null value. Every numeric value prints as `uint64_t`, so C's integer
promotion never applies to printed code.

**Errors.** Evaluation fails on: arithmetic overflow or underflow, use of a
null or dead handle, an extern call outside its contract precondition, a
loop still running at its bound, a full trade buffer, a type mismatch, an
unbound name, a missing function or return, and exhausted call depth. A run
that ends `.ok` therefore performed no contract violation, no overflow, no
invalid handle use and no bound exhaustion.

**Semantics** is parametric in the store: `execStmt` works for any `S` with an
`EngineDb S` instance, and reads and writes storage only through its
operations and its `view`.
-/

namespace Matcher

open EngineDbApi

abbrev Ident := String

inductive Ty where
  | u64
  | code
  | bool
  | order
  | level
  deriving DecidableEq, Repr, Inhabited

inductive Val where
  | u64   : UInt64 → Val
  /-- An enumeration value: equality only, no arithmetic. -/
  | code  : UInt8 → Val
  | bool  : Bool → Val
  /-- An order handle; `none` is NULL. -/
  | order : Option OrderH → Val
  /-- A level handle; `none` is NULL. -/
  | level : Option LevelH → Val
  deriving DecidableEq, Repr, Inhabited

def Val.ty : Val → Ty
  | .u64 _ => .u64
  | .code _ => .code
  | .bool _ => .bool
  | .order _ => .order
  | .level _ => .level

def Ty.default : Ty → Val
  | .u64 => .u64 0
  | .code => .code 0
  | .bool => .bool false
  | .order => .order none
  | .level => .level none

/-- Payload fields of an order row. -/
inductive OField where
  | id | account | side | stpMode | price | qty | remaining
  deriving DecidableEq, Repr

/-- Fields of a level row. `count` (`orders_n`) is read-only. Level totals are
    not in the contract. -/
inductive LField where
  | price | count
  deriving DecidableEq, Repr

inductive UnOp where
  | not
  deriving DecidableEq, Repr

inductive BinOp where
  | add | sub | mul
  | eq | ne | lt | le
  | and | or
  deriving DecidableEq, Repr

inductive Expr where
  | lit     : UInt64 → Expr
  | clit    : UInt8 → Expr
  | blit    : Bool → Expr
  | var     : Ident → Expr
  | un      : UnOp → Expr → Expr
  | bin     : BinOp → Expr → Expr → Expr
  | nullO   : Expr
  | nullL   : Expr
  | isNullO : Expr → Expr
  | isNullL : Expr → Expr
  /-- Read a payload field through an order handle. -/
  | getO    : Expr → OField → Expr
  /-- Read a field through a level handle. -/
  | getL    : Expr → LField → Expr
  deriving Repr, Inhabited

/-- The extern operations: exactly the EngineDb contract. -/
inductive Ext where
  | orderAlloc | levelAlloc
  | orderFree | levelFree
  | setO : OField → Ext
  | setL : LField → Ext
  | hashFind | hashInsert | hashRemove
  | qInsertTail | qRemove | qFirst | qNext
  | owner
  | tFind : Tree → Ext
  | tInsert : Tree → Ext
  | tRemove : Tree → Ext
  | tBest : Tree → Ext
  deriving Repr

inductive Stmt where
  | skip
  | seq    : Stmt → Stmt → Stmt
  | assign : Ident → Expr → Stmt
  | ite    : Expr → Stmt → Stmt → Stmt
  /-- `while (cond)`, at most `n` iterations; still running at the bound is
      an error. The only loop. -/
  | loop   : Nat → Expr → Stmt → Stmt
  /-- Call an EngineDb operation, optionally binding its result. -/
  | ext    : Option Ident → Ext → List Expr → Stmt
  /-- Call a function defined earlier in the program. -/
  | call   : Option Ident → Ident → List Expr → Stmt
  /-- Append a trade (maker id, taker id, price, qty) to the trade buffer. -/
  | emit   : Expr → Expr → Expr → Expr → Stmt
  | ret    : Expr → Stmt
  deriving Repr, Inhabited

def Stmt.block : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (Stmt.block ss)

structure FunDef where
  name   : Ident
  params : List (Ident × Ty)
  locals : List (Ident × Ty)
  ret    : Ty
  /-- An entry point: its printed form resets the trade buffer on entry. -/
  entry  : Bool
  body   : Stmt
  deriving Repr

structure Program where
  funs     : List FunDef
  /-- Trade-buffer capacity per entry call. -/
  tradeCap : Nat
  deriving Repr

inductive Err where
  | type | unbound | overflow | invalidHandle | contract
  | bound | tradeBuffer | fuel | noFun | noReturn | arity
  deriving DecidableEq, Repr

inductive Outcome where
  | normal
  | ret : Val → Outcome
  deriving DecidableEq, Repr

structure St (S : Type) where
  store  : S
  env    : List (Ident × Val)
  trades : List ProcessB.TradeObs

-- ============================================================================
-- Environment
-- ============================================================================

def lookupVar (env : List (Ident × Val)) (x : Ident) : Except Err Val :=
  match env.lookup x with
  | some v => .ok v
  | none => .error .unbound

/-- Assign an existing variable, keeping its type. -/
def setVar (env : List (Ident × Val)) (x : Ident) (v : Val) : Except Err (List (Ident × Val)) :=
  match env.lookup x with
  | none => .error .unbound
  | some old =>
    if old.ty = v.ty then .ok (env.map fun p => if p.1 = x then (x, v) else p)
    else .error .type

-- ============================================================================
-- Arithmetic: fixed width, overflow is an error
-- ============================================================================

def addU (a b : UInt64) : Except Err UInt64 :=
  if a.toNat + b.toNat < 2 ^ 64 then .ok (a + b) else .error .overflow

def subU (a b : UInt64) : Except Err UInt64 :=
  if b.toNat ≤ a.toNat then .ok (a - b) else .error .overflow

def mulU (a b : UInt64) : Except Err UInt64 :=
  if a.toNat * b.toNat < 2 ^ 64 then .ok (a * b) else .error .overflow

def evalBin : BinOp → Val → Val → Except Err Val
  | .add, .u64 a, .u64 b => .u64 <$> addU a b
  | .sub, .u64 a, .u64 b => .u64 <$> subU a b
  | .mul, .u64 a, .u64 b => .u64 <$> mulU a b
  | .eq, .u64 a, .u64 b => .ok (.bool (a == b))
  | .ne, .u64 a, .u64 b => .ok (.bool (a != b))
  | .lt, .u64 a, .u64 b => .ok (.bool (a < b))
  | .le, .u64 a, .u64 b => .ok (.bool (a ≤ b))
  | .eq, .code a, .code b => .ok (.bool (a == b))
  | .ne, .code a, .code b => .ok (.bool (a != b))
  | .eq, .bool a, .bool b => .ok (.bool (a == b))
  | .ne, .bool a, .bool b => .ok (.bool (a != b))
  | .eq, .order a, .order b => .ok (.bool (a == b))
  | .ne, .order a, .order b => .ok (.bool (a != b))
  | .eq, .level a, .level b => .ok (.bool (a == b))
  | .ne, .level a, .level b => .ok (.bool (a != b))
  | .and, .bool a, .bool b => .ok (.bool (a && b))
  | .or, .bool a, .bool b => .ok (.bool (a || b))
  | _, _, _ => .error .type

-- ============================================================================
-- Contract checks, decided on the store's view
-- ============================================================================

section Checks

variable (db : Db)

def liveO (h : OrderH) : Bool := (db.orders h).isSome
def liveL (l : LevelH) : Bool := (db.levels l).isSome
def queuedB (h : OrderH) : Bool := db.lLive.any fun l => (db.queue l).contains h
def inHashB (h : OrderH) : Bool := db.hash.contains h
def inTreeB (t : Tree) (l : LevelH) : Bool := (db.tree t).contains l
def inAnyTreeB (l : LevelH) : Bool := inTreeB db .bids l || inTreeB db .asks l
def priceFreshB (t : Tree) (l : LevelH) : Bool :=
  (db.tree t).all fun l' => db.levelPrice l' != db.levelPrice l

end Checks

def getOField (r : OrderRow) : OField → Val
  | .id => .u64 r.id
  | .account => .u64 r.account
  | .side => .code r.side
  | .stpMode => .code r.stpMode
  | .price => .u64 r.price
  | .qty => .u64 r.qty
  | .remaining => .u64 r.remaining

/-- Write a field: numeric fields take a `u64`, enumeration fields a `code`. -/
def setOField (r : OrderRow) : OField → Val → Except Err OrderRow
  | .id, .u64 v => .ok { r with id := v }
  | .account, .u64 v => .ok { r with account := v }
  | .side, .code v => .ok { r with side := v }
  | .stpMode, .code v => .ok { r with stpMode := v }
  | .price, .u64 v => .ok { r with price := v }
  | .qty, .u64 v => .ok { r with qty := v }
  | .remaining, .u64 v => .ok { r with remaining := v }
  | _, _ => .error .type

section Semantics

variable {S : Type} [EngineDb S]

def viewOf (st : St S) : Db := EngineDb.view st.store

/-- A live order handle, or `invalidHandle`. -/
def liveOrder (st : St S) : Val → Except Err OrderH
  | .order (some h) => if liveO (viewOf st) h then .ok h else .error .invalidHandle
  | .order none => .error .invalidHandle
  | _ => .error .type

def liveLevel (st : St S) : Val → Except Err LevelH
  | .level (some l) => if liveL (viewOf st) l then .ok l else .error .invalidHandle
  | .level none => .error .invalidHandle
  | _ => .error .type

def asU64 : Val → Except Err UInt64
  | .u64 n => .ok n
  | _ => .error .type

def asBool : Val → Except Err Bool
  | .bool b => .ok b
  | _ => .error .type

def evalExpr (st : St S) : Expr → Except Err Val
  | .lit n => .ok (.u64 n)
  | .clit c => .ok (.code c)
  | .blit b => .ok (.bool b)
  | .var x => lookupVar st.env x
  | .un .not e => do
    let b ← asBool (← evalExpr st e)
    .ok (.bool (!b))
  | .bin op a b => do
    let va ← evalExpr st a
    let vb ← evalExpr st b
    evalBin op va vb
  | .nullO => .ok (.order none)
  | .nullL => .ok (.level none)
  | .isNullO e => do
    match ← evalExpr st e with
    | .order h => .ok (.bool h.isNone)
    | _ => .error .type
  | .isNullL e => do
    match ← evalExpr st e with
    | .level l => .ok (.bool l.isNone)
    | _ => .error .type
  | .getO e f => do
    let h ← liveOrder st (← evalExpr st e)
    match EngineDb.readOrder st.store h with
    | some r => .ok (getOField r f)
    | none => .error .invalidHandle
  | .getL e f => do
    let l ← liveLevel st (← evalExpr st e)
    match f with
    | .count =>
      let n := EngineDb.levelCount st.store l
      if n < 2 ^ 64 then .ok (.u64 n.toUInt64) else .error .overflow
    | .price =>
      match EngineDb.readLevel st.store l with
      | some r => .ok (.u64 r.price)
      | none => .error .invalidHandle

/-- Run one extern operation on evaluated arguments: check its contract
    precondition on the view, then call the store. -/
def runExt (st : St S) : Ext → List Val → Except Err (S × Option Val)
  | .orderAlloc, [] =>
    let r := EngineDb.orderAlloc st.store
    .ok (r.2, some (.order r.1))
  | .levelAlloc, [] =>
    let r := EngineDb.levelAlloc st.store
    .ok (r.2, some (.level r.1))
  | .orderFree, [vh] => do
    let h ← liveOrder st vh
    if queuedB (viewOf st) h || inHashB (viewOf st) h then .error .contract
    else .ok (EngineDb.orderFree st.store h, none)
  | .levelFree, [vl] => do
    let l ← liveLevel st vl
    if inAnyTreeB (viewOf st) l || !((viewOf st).queue l).isEmpty then .error .contract
    else .ok (EngineDb.levelFree st.store l, none)
  | .setO f, [vh, vv] => do
    let h ← liveOrder st vh
    if f = .id && inHashB (viewOf st) h then .error .contract
    else
      match EngineDb.readOrder st.store h with
      | none => .error .invalidHandle
      | some r => do
        let r' ← setOField r f vv
        .ok (EngineDb.writeOrder st.store h r', none)
  | .setL f, [vl, vv] => do
    let l ← liveLevel st vl
    let v ← asU64 vv
    match EngineDb.readLevel st.store l with
    | none => .error .invalidHandle
    | some r =>
      match f with
      | .price =>
        if inAnyTreeB (viewOf st) l then .error .contract
        else .ok (EngineDb.writeLevel st.store l { r with price := v }, none)
      | .count => .error .type
  | .hashFind, [vid] => do
    let id ← asU64 vid
    .ok (st.store, some (.order (EngineDb.hashFind st.store id)))
  | .hashInsert, [vh] => do
    let h ← liveOrder st vh
    if inHashB (viewOf st) h then .error .contract
    else
      let r := EngineDb.hashInsert st.store h
      .ok (r.2, some (.bool r.1))
  | .hashRemove, [vh] => do
    let h ← liveOrder st vh
    if inHashB (viewOf st) h then .ok (EngineDb.hashRemove st.store h, none)
    else .error .contract
  | .qInsertTail, [vl, vh] => do
    let l ← liveLevel st vl
    let h ← liveOrder st vh
    if queuedB (viewOf st) h then .error .contract
    else .ok (EngineDb.qInsertTail st.store l h, none)
  | .qRemove, [vl, vh] => do
    let l ← liveLevel st vl
    let h ← liveOrder st vh
    if ((viewOf st).queue l).contains h then .ok (EngineDb.qRemove st.store l h, none)
    else .error .contract
  | .qFirst, [vl] => do
    let l ← liveLevel st vl
    .ok (st.store, some (.order (EngineDb.qFirst st.store l)))
  | .qNext, [vh] => do
    let h ← liveOrder st vh
    if queuedB (viewOf st) h then .ok (st.store, some (.order (EngineDb.qNext st.store h)))
    else .error .contract
  | .owner, [vh] => do
    let h ← liveOrder st vh
    .ok (st.store, some (.level (EngineDb.owner st.store h)))
  | .tFind t, [vp] => do
    let p ← asU64 vp
    .ok (st.store, some (.level (EngineDb.tFind st.store t p)))
  | .tInsert t, [vl] => do
    let l ← liveLevel st vl
    if inAnyTreeB (viewOf st) l || !priceFreshB (viewOf st) t l then .error .contract
    else .ok (EngineDb.tInsert st.store t l, none)
  | .tRemove t, [vl] => do
    let l ← liveLevel st vl
    if inTreeB (viewOf st) t l then .ok (EngineDb.tRemove st.store t l, none)
    else .error .contract
  | .tBest t, [] => .ok (st.store, some (.level (EngineDb.tBest st.store t)))
  | _, _ => .error .arity

def bindResult (env : List (Ident × Val)) : Option Ident → Option Val →
    Except Err (List (Ident × Val))
  | none, _ => .ok env
  | some x, some v => setVar env x v
  | some _, none => .error .type

def bindParams : List (Ident × Ty) → List Val → Except Err (List (Ident × Val))
  | [], [] => .ok []
  | (x, t) :: ps, v :: vs =>
    if v.ty = t then ((x, v) :: ·) <$> bindParams ps vs else .error .type
  | _, _ => .error .arity

def lookupFun (P : Program) (f : Ident) : Except Err FunDef :=
  match P.funs.find? (·.name == f) with
  | some fd => .ok fd
  | none => .error .noFun

def toNatTrade (m t p q : UInt64) : ProcessB.TradeObs :=
  { makerId := m.toNat, takerId := t.toNat, price := p.toNat, qty := q.toNat }

/-- Statement semantics. `fuel` bounds nesting and call depth only;
    running out of it is the `fuel` error. Loop iterations are bounded by
    each loop's own literal bound. -/
def execStmt (P : Program) : Nat → Stmt → St S → Except Err (St S × Outcome)
  | 0, _, _ => .error .fuel
  | f + 1, s, st =>
    match s with
    | .skip => .ok (st, .normal)
    | .seq a b => do
      let (st1, o) ← execStmt P f a st
      match o with
      | .ret v => .ok (st1, .ret v)
      | .normal => execStmt P f b st1
    | .assign x e => do
      let v ← evalExpr st e
      let env ← setVar st.env x v
      .ok ({ st with env := env }, .normal)
    | .ite c a b => do
      let cb ← asBool (← evalExpr st c)
      if cb then execStmt P f a st else execStmt P f b st
    | .loop n c body =>
      let r := (List.range n).foldl
        (fun (acc : Except Err (St S × Outcome × Bool)) _ =>
          match acc with
          | .ok (st', .normal, false) =>
            match evalExpr st' c with
            | .ok (.bool true) =>
              match execStmt P f body st' with
              | .ok (st'', o) => .ok (st'', o, false)
              | .error e => .error e
            | .ok (.bool false) => .ok (st', .normal, true)
            | .ok _ => .error .type
            | .error e => .error e
          | other => other)
        (.ok (st, .normal, false))
      match r with
      | .error e => .error e
      | .ok (st', .ret v, _) => .ok (st', .ret v)
      | .ok (st', .normal, true) => .ok (st', .normal)
      | .ok (st', .normal, false) =>
        match evalExpr st' c with
        | .ok (.bool false) => .ok (st', .normal)
        | .ok (.bool true) => .error .bound
        | .ok _ => .error .type
        | .error e => .error e
    | .ext dst op args => do
      let vals ← args.mapM (evalExpr st)
      let (store', res) ← runExt st op vals
      let env ← bindResult st.env dst res
      .ok ({ st with store := store', env := env }, .normal)
    | .call dst fname args => do
      let fd ← lookupFun P fname
      let vals ← args.mapM (evalExpr st)
      let penv ← bindParams fd.params vals
      let env0 := penv ++ fd.locals.map fun (x, t) => (x, t.default)
      let (st1, o) ← execStmt P f fd.body { st with env := env0 }
      match o with
      | .normal => .error .noReturn
      | .ret v =>
        if v.ty = fd.ret then do
          let env ← bindResult st.env dst (some v)
          .ok ({ st1 with env := env }, .normal)
        else .error .type
    | .emit m t p q => do
      let vm ← asU64 (← evalExpr st m)
      let vt ← asU64 (← evalExpr st t)
      let vp ← asU64 (← evalExpr st p)
      let vq ← asU64 (← evalExpr st q)
      if st.trades.length < P.tradeCap then
        .ok ({ st with trades := st.trades ++ [toNatTrade vm vt vp vq] }, .normal)
      else .error .tradeBuffer
    | .ret e => do
      let v ← evalExpr st e
      .ok (st, .ret v)

/-- Run an entry function on a store: its return value, the final store, and
    the trades it emitted. -/
def runEntry (P : Program) (fuel : Nat) (fname : Ident) (args : List Val) (s : S) :
    Except Err (Val × S × List ProcessB.TradeObs) := do
  let fd ← lookupFun P fname
  let penv ← bindParams fd.params args
  let env0 := penv ++ fd.locals.map fun (x, t) => (x, t.default)
  let (st1, o) ← execStmt P fuel fd.body { store := s, env := env0, trades := [] }
  match o with
  | .normal => .error .noReturn
  | .ret v => if v.ty = fd.ret then .ok (v, st1.store, st1.trades) else .error .type

end Semantics

end Matcher
