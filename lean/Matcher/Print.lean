import Matcher.Lang

/-!
# Printing the matcher language as C

`Print.program` renders a `Program` as one C11 translation unit that includes
`c/gen/engine_db.h` and calls nothing else from the data layer. The dialect
follows AMCC's printer: `<stdint.h>` fixed-width types, every compound
expression parenthesised, every integer literal written `UINT64_C(n)`. Both
`u64` and `code` values print as `uint64_t`.

Where the semantics raises an error, the printed C calls `me_trap(k)` (which
aborts), with `k` the error class (`trapCode`): 1 for overflow in
`me_add`/`me_sub`/`me_mul` and a zero divisor in `me_div`, 2 for a loop still
running at its bound, 3 for a full trade buffer, 4 for control reaching the end
of a function, 5 for a malformed extern call. So a compiled run either agrees
with a semantic run that ends `.ok`, or stops. A test harness may define
`ME_TRAP_REPORT` to learn the class before the abort (Phase 5 semantics test);
without it the class is unused.
Contract violations on handles are not re-checked in C; the proof rules them
out, and Phase 5 tests the data layer against the contract.

Identifiers are printed as given: they must be valid C identifiers, and must
not start with `me_` or `ME_`, which the printer reserves.
-/

namespace Matcher.Print

open EngineDbApi Matcher

def cTy : Ty → String
  | .u64 => "uint64_t"
  | .code => "uint64_t"
  | .bool => "bool"
  | .order => "ME_OrderH"
  | .level => "ME_LevelH"

def cDefault : Ty → String
  | .u64 => "UINT64_C(0)"
  | .code => "UINT64_C(0)"
  | .bool => "false"
  | .order => "((ME_OrderH)NULL)"
  | .level => "((ME_LevelH)NULL)"

def oField : OField → String
  | .id => "id" | .account => "account" | .side => "side" | .stpMode => "stp_mode"
  | .price => "price" | .qty => "qty" | .remaining => "remaining"

def lField : LField → String
  | .price => "price" | .count => "count"

def treeName : Tree → String
  | .bids => "bids"
  | .asks => "asks"

def expr : Expr → String
  | .lit n => s!"UINT64_C({n.toNat})"
  | .clit c => s!"UINT64_C({c.toNat})"
  | .blit b => if b then "true" else "false"
  | .var x => x
  | .un .not e => s!"(!{expr e})"
  | .bin op a b =>
    match op with
    | .add => s!"me_add({expr a}, {expr b})"
    | .sub => s!"me_sub({expr a}, {expr b})"
    | .mul => s!"me_mul({expr a}, {expr b})"
    | .div => s!"me_div({expr a}, {expr b})"
    | .eq => s!"({expr a} == {expr b})"
    | .ne => s!"({expr a} != {expr b})"
    | .lt => s!"({expr a} < {expr b})"
    | .le => s!"({expr a} <= {expr b})"
    | .and => s!"({expr a} && {expr b})"
    | .or => s!"({expr a} || {expr b})"
  | .nullO => cDefault .order
  | .nullL => cDefault .level
  | .isNullO e => s!"({expr e} == NULL)"
  | .isNullL e => s!"({expr e} == NULL)"
  | .getO e f => s!"ME_order_get_{oField f}({expr e})"
  | .getL e f => s!"ME_level_get_{lField f}({expr e})"
  | .capacity => "ME_capacity()"
  | .count => "ME_order_count()"

def args (es : List Expr) : String := ", ".intercalate (es.map expr)

/-- The trap class of a semantic error, as the printed C reports it. -/
def trapCode : Err → Nat
  | .overflow => 1
  | .bound => 2
  | .tradeBuffer => 3
  | .noReturn => 4
  | .arity => 5
  | _ => 0

/-- A bound as C: the same quantity the semantics uses (`boundVal`). -/
def bound : Bound → String
  | .lit n => s!"UINT64_C({n})"
  | .capPlus k => s!"me_add(ME_capacity(), UINT64_C({k}))"

/-- The C call of an extern operation, or `none` for a malformed one, which
    the semantics rejects (`arity`/`type`) and the printer turns into a trap. -/
def extCall : Ext → List Expr → Option String
  | .orderAlloc, [] => some "ME_order_alloc()"
  | .levelAlloc, [] => some "ME_level_alloc()"
  | .orderFree, [h] => some s!"ME_order_free({expr h})"
  | .levelFree, [l] => some s!"ME_level_free({expr l})"
  | .setO f, [h, v] => some s!"ME_order_set_{oField f}({expr h}, {expr v})"
  | .setL .price, [l, v] => some s!"ME_level_set_price({expr l}, {expr v})"
  | .hashFind, [i] => some s!"ME_hash_find({expr i})"
  | .hashInsert, [h] => some s!"ME_hash_insert({expr h})"
  | .hashRemove, [h] => some s!"ME_hash_remove({expr h})"
  | .qInsertTail, [l, h] => some s!"ME_queue_insert_tail({expr l}, {expr h})"
  | .qRemove, [l, h] => some s!"ME_queue_remove({expr l}, {expr h})"
  | .qFirst, [l] => some s!"ME_queue_first({expr l})"
  | .qNext, [h] => some s!"ME_queue_next({expr h})"
  | .owner, [h] => some s!"ME_order_owner({expr h})"
  | .tFind t, [p] => some s!"ME_{treeName t}_find({expr p})"
  | .tInsert t, [l] => some s!"ME_{treeName t}_insert({expr l})"
  | .tRemove t, [l] => some s!"ME_{treeName t}_remove({expr l})"
  | .tBest t, [] => some s!"ME_{treeName t}_best()"
  | _, _ => none

/-- Does the operation return a value? -/
def extReturns : Ext → Bool
  | .orderAlloc | .levelAlloc | .hashFind | .hashInsert | .qFirst | .qNext
  | .owner | .tFind _ | .tBest _ => true
  | _ => false

def pad (n : Nat) : String := "".pushn ' ' (2 * n)

/-- Print a statement at indentation `ind`; `depth` names loop counters. -/
def stmt (ind depth : Nat) : Stmt → String
  | .skip => ""
  | .seq a b => stmt ind depth a ++ stmt ind depth b
  | .assign x e => s!"{pad ind}{x} = {expr e};\n"
  | .ite c a b =>
    s!"{pad ind}if ((bool){expr c}) \{\n" ++ stmt (ind + 1) depth a ++
    s!"{pad ind}} else \{\n" ++ stmt (ind + 1) depth b ++ s!"{pad ind}}\n"
  | .loop bnd c body =>
    let k := s!"me_k{depth}"
    let n := s!"me_n{depth}"
    s!"{pad ind}for (uint64_t {k} = UINT64_C(0), {n} = {bound bnd};; {k} = {k} + UINT64_C(1)) \{\n" ++
    s!"{pad (ind + 1)}if (!{expr c}) break;\n" ++
    s!"{pad (ind + 1)}if ({k} == {n}) me_trap(2);\n" ++
    stmt (ind + 1) (depth + 1) body ++ s!"{pad ind}}\n"
  | .ext dst op es =>
    match extCall op es, dst with
    | none, _ => s!"{pad ind}me_trap(5);\n"
    | some c, some x => s!"{pad ind}{x} = {c};\n"
    | some c, none => if extReturns op then s!"{pad ind}(void){c};\n" else s!"{pad ind}{c};\n"
  | .call dst f es =>
    match dst with
    | some x => s!"{pad ind}{x} = {f}({args es});\n"
    | none => s!"{pad ind}(void){f}({args es});\n"
  | .emit m t p q => s!"{pad ind}me_emit({expr m}, {expr t}, {expr p}, {expr q});\n"
  | .ret e => s!"{pad ind}return {expr e};\n"

def decl (p : Ident × Ty) : String := s!"{cTy p.2} {p.1}"

def funDef (fd : FunDef) : String :=
  let ps := if fd.params.isEmpty then "void" else ", ".intercalate (fd.params.map decl)
  let locals := String.join (fd.locals.map fun (x, t) => s!"  {cTy t} {x} = {cDefault t};\n")
  let voids := String.join ((fd.params ++ fd.locals).map fun (x, _) => s!"  (void){x};\n")
  let reset := if fd.entry then "  me_ntrades = UINT64_C(0);\n  ME_trade_reset();\n" else ""
  s!"{cTy fd.ret} {fd.name}({ps}) \{\n" ++ locals ++ voids ++ reset ++
    stmt 1 0 fd.body ++ "  me_trap(4);\n}\n"

def preamble (tradeCap : Bound) : String :=
  "/* Generated from lean/Matcher by Matcher.Print.program. Do not edit. */\n" ++
  "#include \"engine_db.h\"\n#include <stdbool.h>\n#include <stdint.h>\n#include <stdlib.h>\n\n" ++
  "static uint64_t me_ntrades;\n\n" ++
  "#ifdef ME_TRAP_REPORT\nvoid ME_TRAP_REPORT(unsigned k);\n#endif\n" ++
  "_Noreturn static inline void me_trap(unsigned k) {\n" ++
  "#ifdef ME_TRAP_REPORT\n  ME_TRAP_REPORT(k);\n#else\n  (void)k;\n#endif\n  abort();\n}\n" ++
  "static inline __attribute__((unused)) uint64_t me_add(uint64_t a, uint64_t b) {\n" ++
  "  uint64_t r;\n  if (__builtin_add_overflow(a, b, &r)) me_trap(1);\n  return r;\n}\n" ++
  "static inline __attribute__((unused)) uint64_t me_sub(uint64_t a, uint64_t b) {\n" ++
  "  uint64_t r;\n  if (__builtin_sub_overflow(a, b, &r)) me_trap(1);\n  return r;\n}\n" ++
  "static inline __attribute__((unused)) uint64_t me_mul(uint64_t a, uint64_t b) {\n" ++
  "  uint64_t r;\n  if (__builtin_mul_overflow(a, b, &r)) me_trap(1);\n  return r;\n}\n" ++
  "static inline __attribute__((unused)) uint64_t me_div(uint64_t a, uint64_t b) {\n" ++
  "  if (b == UINT64_C(0)) me_trap(1);\n  return a / b;\n}\n" ++
  "static inline __attribute__((unused)) void me_emit(uint64_t m, uint64_t t, uint64_t p, uint64_t q) {\n" ++
  s!"  if (me_ntrades >= {bound tradeCap}) me_trap(3);\n" ++
  "  ME_trade_emit(m, t, p, q);\n" ++
  "  me_ntrades = me_ntrades + UINT64_C(1);\n}\n\n"

def program (P : Program) : String :=
  preamble P.tradeCap ++ "\n".intercalate (P.funs.map funDef)

end Matcher.Print
