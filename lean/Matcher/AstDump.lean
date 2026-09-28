import Matcher.Program

/-!
# The matcher AST as an S-expression (plan v2 Phase 5, item 4)

`dump` renders a `Program` directly from its syntax tree, not through the C
printer. `tests/printer/reparse.py` parses `c/gen/matcher.c` with pycparser,
maps the C back to the same S-expression form, and the two must be equal.

The dump erases exactly what the C printing identifies, so that the comparison
is about the tree and nothing else:
* `code` values and types print as `uint64_t`: `Ty.code` dumps as `u64` and
  `Expr.clit n` as `(lit n)`;
* a null test prints as `(e == NULL)` for both handle types: `isNullO` and
  `isNullL` dump as `(isnull e)`;
* `Stmt.seq`/`Stmt.block` nesting is flattened into statement lists, and
  `skip` disappears;
* handle types keep their names (`order`, `level`), which C keeps too.
-/

namespace AstDump

open Matcher EngineDbApi

def ty : Ty → String
  | .u64 | .code => "u64"
  | .bool => "bool"
  | .order => "order"
  | .level => "level"

def ofield : OField → String
  | .id => "id" | .account => "account" | .side => "side" | .stpMode => "stp_mode"
  | .price => "price" | .qty => "qty" | .remaining => "remaining"

def lfield : LField → String
  | .price => "price" | .count => "count"

def binop : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .and => "and" | .or => "or"

def expr : Expr → String
  | .lit n => s!"(lit {n.toNat})"
  | .clit c => s!"(lit {c.toNat})"
  | .blit b => s!"(bool {if b then 1 else 0})"
  | .var x => s!"(var {x})"
  | .un .not e => s!"(not {expr e})"
  | .bin op a b => s!"({binop op} {expr a} {expr b})"
  | .nullO => "(null order)"
  | .nullL => "(null level)"
  | .isNullO e => s!"(isnull {expr e})"
  | .isNullL e => s!"(isnull {expr e})"
  | .getO e f => s!"(getO {ofield f} {expr e})"
  | .getL e f => s!"(getL {lfield f} {expr e})"
  | .capacity => "(capacity)"
  | .count => "(count)"

def treeName : Tree → String
  | .bids => "bids"
  | .asks => "asks"

def ext : Ext → String
  | .orderAlloc => "order_alloc" | .levelAlloc => "level_alloc"
  | .orderFree => "order_free" | .levelFree => "level_free"
  | .setO f => s!"order_set_{ofield f}" | .setL f => s!"level_set_{lfield f}"
  | .hashFind => "hash_find" | .hashInsert => "hash_insert" | .hashRemove => "hash_remove"
  | .qInsertTail => "queue_insert_tail" | .qRemove => "queue_remove"
  | .qFirst => "queue_first" | .qNext => "queue_next" | .owner => "order_owner"
  | .tFind t => s!"{treeName t}_find" | .tInsert t => s!"{treeName t}_insert"
  | .tRemove t => s!"{treeName t}_remove" | .tBest t => s!"{treeName t}_best"

def bound : Bound → String
  | .lit n => s!"(lit {n})"
  | .capPlus k => s!"(capplus {k})"

def args (es : List Expr) : String := " ".intercalate (es.map expr)

mutual
def stmts : Stmt → List String
  | .skip => []
  | .seq a b => stmts a ++ stmts b
  | .assign x e => [s!"(assign {x} {expr e})"]
  | .ite c a b => [s!"(if {expr c} (block {" ".intercalate (stmts a)}) (block {" ".intercalate (stmts b)}))"]
  | .loop bnd c body => [s!"(loop {bound bnd} {expr c} (block {" ".intercalate (stmts body)}))"]
  | .ext dst op es =>
    [s!"(ext {dst.getD "_"} {ext op} ({args es}))"]
  | .call dst f es => [s!"(call {dst.getD "_"} {f} ({args es}))"]
  | .emit m t p q => [s!"(emit {expr m} {expr t} {expr p} {expr q})"]
  | .ret e => [s!"(ret {expr e})"]
end

def decl (p : Ident × Ty) : String := s!"({p.1} {ty p.2})"

def funDef (fd : FunDef) : String :=
  s!"(fun {fd.name} {ty fd.ret} {if fd.entry then "entry" else "plain"} " ++
  s!"(params {" ".intercalate (fd.params.map decl)}) (locals {" ".intercalate (fd.locals.map decl)}) " ++
  s!"(block {" ".intercalate (stmts fd.body)}))"

def dump (P : Program) : String :=
  s!"(program (tradecap {bound P.tradeCap})\n" ++ "\n".intercalate (P.funs.map funDef) ++ ")\n"

end AstDump
