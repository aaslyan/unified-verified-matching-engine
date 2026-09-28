#!/usr/bin/env bash
# Printer check (plan v2 Phase 5, item 4): reparse c/gen/matcher.c with
# pycparser (tests/printer/reparse.py) and diff the recovered tree against the
# Lean AST dumped directly from lean/Matcher/Program.lean (lean/Matcher/AstDump.lean).
set -euo pipefail
cd "$(dirname "$0")/../.."
out="$(mktemp -d)"; trap 'rm -rf "$out"' EXIT
lake build Matcher.AstDump >/dev/null
lake env lean --run lean/Matcher/DumpAst.lean > "$out/lean.sexp"
python3 tests/printer/reparse.py "${1:-c/gen/matcher.c}" > "$out/c.sexp"
if diff -u "$out/lean.sexp" "$out/c.sexp"; then
  echo "printer: c/gen/matcher.c reparses to the Lean AST ($(($(wc -l < "$out/lean.sexp") - 1)) functions, $(wc -c < "$out/lean.sexp") bytes of tree)"
else
  echo "printer: MISMATCH"; exit 1
fi
