#!/usr/bin/env bash
# Semantics test (plan v2 Phase 5, item 3): random programs in the matcher
# language, run under execStmt (lean/Matcher/SemTest.lean) and compiled under
# gcc -O0, gcc -O2 and clang -O2 with the printed C (Matcher.Print). The
# outcome must agree exactly: the same value, order count and trades, or a trap
# of the same class. Nothing is filtered.
# Usage: tests/semantics/run.sh [seed] [programs] [capacity]
set -euo pipefail
cd "$(dirname "$0")/../.."
seed="${1:-1}"; n="${2:-200}"; cap="${3:-3}"
out="$(mktemp -d)"; trap 'rm -rf "$out"' EXIT
fail=0
lake build Matcher.Print >/dev/null
lake build semtest >/dev/null
gen="$(.lake/build/bin/semtest "$seed" "$n" "$cap" "$out")"
echo "$gen"
# printer check on every generated program: reparse its C, compare with its tree
pr=0
for ((k = 0; k < n; k++)); do
  python3 tests/printer/reparse.py "$out/prog$k.c" > "$out/prog$k.re"
  if cmp -s "$out/prog$k.sexp" "$out/prog$k.re"; then pr=$((pr + 1))
  else echo "PRINTER MISMATCH program $k"; diff "$out/prog$k.sexp" "$out/prog$k.re" | head -5; fail=1; fi
done
echo "printer (reparse of each generated program): $pr/$n agree"
configs=("gcc -O0" "gcc -O2" "clang -O2")
for cfg in "${configs[@]}"; do
  set -- $cfg; cc=$1; opt=$2
  tag="$cc$opt"
  CF="-std=c11 $opt -w -Ic/gen -Ic/include"
  $cc $CF -c -o "$out/h.$tag.o" tests/semantics/harness.c
  $cc $CF -c -o "$out/a.$tag.o" c/gen/engine_db_adapter.c
  $cc $CF -c -o "$out/d.$tag.o" c/src/matching_engine_gen.c
  agree=0
  for ((k = 0; k < n; k++)); do
    $cc $CF -DME_TRAP_REPORT=harness_trap -c -o "$out/p.o" "$out/prog$k.c"
    $cc -o "$out/p" "$out/p.o" "$out/h.$tag.o" "$out/a.$tag.o" "$out/d.$tag.o"
    got="$("$out/p" "$cap" || echo "crash $?")"
    exp="$(cat "$out/prog$k.exp")"
    if [ "$got" == "$exp" ]; then agree=$((agree + 1))
    else
      echo "MISMATCH seed $seed program $k ($cc $opt): lean: $exp | c: $got"
      cp "$out/prog$k.c" "/tmp/semtest_mismatch_${seed}_${k}.c"
      fail=1
    fi
  done
  echo "semantics ($cc $opt): $agree/$n agree"
done
exit $fail
