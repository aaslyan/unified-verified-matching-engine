#!/usr/bin/env python3
"""Printer check (plan v2 Phase 5, item 4).

Parses a printed C file (default c/gen/matcher.c) with pycparser, independently
of the Lean printer, maps the C back to the matcher language's syntax tree, and
prints that tree in the S-expression form of lean/Matcher/AstDump.lean. The
caller diffs it against the dump of the Lean AST (tests/printer/run.sh).

The mapping inverts the printing conventions documented in lean/Matcher/Print.lean:
UINT64_C(n) is a literal, me_add/me_sub/me_mul/me_div are arithmetic,
ME_order_get_*/ME_level_get_*/ME_capacity/ME_order_count are reads, a value-
returning or void ME_* call in statement position is an extern operation,
the for-loop with counters me_k/me_n is a bounded loop, me_emit is the trade
sink. Anything it does not recognise is an error: the reparse accepts only the
printer's language.
"""
import subprocess, sys
from pycparser import c_parser, c_ast

VALUE_EXT = {"order_alloc", "level_alloc", "hash_find", "hash_insert", "queue_first", "queue_next",
             "order_owner", "bids_find", "asks_find", "bids_best", "asks_best"}
BIN = {"==": "eq", "!=": "ne", "<": "lt", "<=": "le", "&&": "and", "||": "or"}
ARITH = {"me_add": "add", "me_sub": "sub", "me_mul": "mul", "me_div": "div"}
TY = {"uint64_t": "u64", "bool": "bool", "_Bool": "bool", "ME_OrderH": "order", "ME_LevelH": "level"}

class Unrecognised(Exception):
    pass

def bad(node, what):
    raise Unrecognised(f"{what}: {node.coord if node is not None else ''} {type(node).__name__}")

def tyname(t):
    while isinstance(t, (c_ast.TypeDecl,)):
        t = t.type
    if isinstance(t, c_ast.IdentifierType):
        return TY[" ".join(t.names)]
    bad(t, "type")

def lit(node):
    if isinstance(node, c_ast.FuncCall) and isinstance(node.name, c_ast.ID) and node.name.name == "UINT64_C":
        c = node.args.exprs[0]
        return int(c.value.rstrip("uUlL"))
    return None

def fname(node):
    return node.name.name if isinstance(node, c_ast.FuncCall) and isinstance(node.name, c_ast.ID) else None

def args(node):
    return node.args.exprs if node.args else []

def expr(e):
    n = lit(e)
    if n is not None:
        return f"(lit {n})"
    if isinstance(e, c_ast.ID):
        if e.name == "true": return "(bool 1)"
        if e.name == "false": return "(bool 0)"
        return f"(var {e.name})"
    if isinstance(e, c_ast.Cast) and isinstance(e.expr, c_ast.ID) and e.expr.name == "NULL":
        return "(null order)" if tyname(e.to_type.type) == "order" else "(null level)"
    if isinstance(e, c_ast.UnaryOp) and e.op == "!":
        return f"(not {expr(e.expr)})"
    if isinstance(e, c_ast.BinaryOp):
        if e.op == "==" and isinstance(e.right, c_ast.ID) and e.right.name == "NULL":
            return f"(isnull {expr(e.left)})"
        if e.op in BIN:
            return f"({BIN[e.op]} {expr(e.left)} {expr(e.right)})"
    f = fname(e)
    if f in ARITH:
        a, b = args(e)
        return f"({ARITH[f]} {expr(a)} {expr(b)})"
    if f == "ME_capacity": return "(capacity)"
    if f == "ME_order_count": return "(count)"
    if f and f.startswith("ME_order_get_"):
        return f"(getO {f[len('ME_order_get_'):]} {expr(args(e)[0])})"
    if f and f.startswith("ME_level_get_"):
        return f"(getL {f[len('ME_level_get_'):]} {expr(args(e)[0])})"
    bad(e, "expression")

def bound(e):
    n = lit(e)
    if n is not None:
        return f"(lit {n})"
    if fname(e) == "me_add" and fname(args(e)[0]) == "ME_capacity":
        return f"(capplus {lit(args(e)[1])})"
    bad(e, "loop bound")

def block(items):
    return "(block " + " ".join(s for it in items for s in stmt(it)) + ")"

def compound(c):
    return c.block_items or []

def stmt(s):
    if isinstance(s, c_ast.If):
        cond = s.cond
        if not (isinstance(cond, c_ast.Cast) and tyname(cond.to_type.type) == "bool"):
            bad(s, "if condition cast")
        return [f"(if {expr(cond.expr)} {block(compound(s.iftrue))} {block(compound(s.iffalse))})"]
    if isinstance(s, c_ast.For):
        decls = s.init.decls
        k, n = decls[0].name, decls[1].name
        if not (k.startswith("me_k") and n.startswith("me_n") and lit(decls[0].init) == 0): bad(s, "loop init")
        body = compound(s.stmt)
        brk, trap = body[0], body[1]
        if not (isinstance(brk, c_ast.If) and isinstance(brk.iftrue, c_ast.Break)
                and isinstance(brk.cond, c_ast.UnaryOp) and brk.cond.op == "!"):
            bad(s, "loop exit")
        if not (isinstance(trap, c_ast.If) and fname(trap.iftrue) == "me_trap"
                and lit(args(trap.iftrue)[0]) is None and args(trap.iftrue)[0].value == "2"):
            bad(s, "loop bound trap")
        return [f"(loop {bound(decls[1].init)} {expr(brk.cond.expr)} {block(body[2:])})"]
    if isinstance(s, c_ast.Return):
        return [f"(ret {expr(s.expr)})"]
    if isinstance(s, c_ast.Assignment) and s.op == "=":
        x = s.lvalue.name
        f = fname(s.rvalue)
        if f and f.startswith("ME_") and f[3:] in VALUE_EXT:
            return [f"(ext {x} {f[3:]} ({' '.join(expr(a) for a in args(s.rvalue))}))"]
        if f and not f.startswith("ME_") and not f.startswith("me_") and f != "UINT64_C":
            return [f"(call {x} {f} ({' '.join(expr(a) for a in args(s.rvalue))}))"]
        return [f"(assign {x} {expr(s.rvalue)})"]
    call = s.expr if isinstance(s, c_ast.Cast) else s
    f = fname(call)
    if f == "me_emit":
        m, t, p, q = args(call)
        return [f"(emit {expr(m)} {expr(t)} {expr(p)} {expr(q)})"]
    if f and f.startswith("ME_"):
        return [f"(ext _ {f[3:]} ({' '.join(expr(a) for a in args(call))}))"]
    if f and not f.startswith("me_"):
        return [f"(call _ {f} ({' '.join(expr(a) for a in args(call))}))"]
    bad(s, "statement")

def fundef(fd):
    d = fd.decl
    ret = tyname(d.type.type)
    ps = []
    fparams = d.type.args.params if d.type.args else []
    for p in fparams:
        if isinstance(p, c_ast.Typename):   # (void)
            continue
        ps.append(f"({p.name} {tyname(p.type)})")
    items = compound(fd.body)
    locs, i = [], 0
    while i < len(items) and isinstance(items[i], c_ast.Decl):
        locs.append(f"({items[i].name} {tyname(items[i].type)})"); i += 1
    while i < len(items) and isinstance(items[i], c_ast.Cast) and isinstance(items[i].expr, c_ast.ID):
        i += 1                               # (void)x;
    entry = "plain"
    if i + 1 < len(items) and isinstance(items[i], c_ast.Assignment) and items[i].lvalue.name == "me_ntrades" \
            and fname(items[i + 1]) == "ME_trade_reset":
        entry, i = "entry", i + 2
    last = items[-1]
    if not (fname(last) == "me_trap" and args(last)[0].value == "4"):
        bad(last, "function trailer")
    body = block(items[i:-1])
    return f"(fun {d.name} {ret} {entry} (params {' '.join(ps)}) (locals {' '.join(locs)}) {body})"

def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "c/gen/matcher.c"
    pre = subprocess.run(["gcc", "-E", "-P", "-nostdinc", "-Itests/printer/stub", "-Ic/gen",
                          "-D__attribute__(x)=", "-D_Noreturn=", path],
                         check=True, capture_output=True, text=True).stdout
    ast = c_parser.CParser().parse(pre, path)
    funs, tradecap = [], None
    for ext in ast.ext:
        if not isinstance(ext, c_ast.FuncDef):
            continue
        if "static" in (ext.decl.storage or []):
            if ext.decl.name == "me_emit":
                cond = compound(ext.body)[0].cond
                tradecap = bound(cond.right)
            continue
        funs.append(fundef(ext))
    print(f"(program (tradecap {tradecap})\n" + "\n".join(funs) + ")")

try:
    main()
except Unrecognised as e:
    print(f"reparse: not the printer's language: {e}", file=sys.stderr)
    sys.exit(1)
