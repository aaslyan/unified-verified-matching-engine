#!/usr/bin/env bash
# Contract tests (plan v2 Phase 5, item 1): the EngineDb laws against the
# adapter + handwritten data layer as linked under the matcher, at several
# capacities, under gcc -O2 and clang -O2.
# Usage: tests/contract/run.sh [first_seed] [seeds] [ops]
# MUTANT=1|2|3 runs one documented adapter mutation and succeeds only when the
# contract test catches it:
#   1 engine_db_adapter.c:70, `>= g_cap` -> `> g_cap`; orderAlloc_law.
#   2 engine_db_adapter.c:107, remove an existing equal-id row before insert;
#     hashInsert_law / hash_insert_refused.
#   3 engine_db_adapter.c:95-98, omit the owner-level total adjustment;
#     private level-total check.
set -euo pipefail
cd "$(dirname "$0")/../.."
first="${1:-1}"; seeds="${2:-50}"; ops="${3:-3000}"
out="$(mktemp -d)"; trap 'rm -rf "$out"' EXIT
ccs="${CC:-gcc clang}"
base_cflags="-std=c11 -Wall -Wextra -Werror -Ic/gen -Ic/include"
opt_cflags="${CFLAGS:--O2}"
adapter=c/gen/engine_db_adapter.c
if [ -n "${MUTANT:-}" ]; then
  cp "$adapter" "$out/engine_db_adapter.c"
  adapter="$out/engine_db_adapter.c"
  python3 - "$adapter" "$MUTANT" <<'PY'
import sys
p, mutant = sys.argv[1:]
s = open(p).read()
if mutant == "1":
    old, new = "order_pool_n >= g_cap", "order_pool_n > g_cap"
elif mutant == "2":
    old = "bool ME_hash_insert(ME_OrderH o) { return EngineDb_ind_order_InsertMaybe(O(o)); }"
    new = """bool ME_hash_insert(ME_OrderH o) {
    struct Order *old = EngineDb_ind_order_Find(O(o)->id);
    if (old) EngineDb_ind_order_Remove(old);
    return EngineDb_ind_order_InsertMaybe(O(o));
}"""
elif mutant == "3":
    old = """    if (o->orders_inlist && o->p_price_level) {
        struct PriceLevel *l = o->p_price_level;
        l->total_qty = (l->total_qty - o->remaining_qty) + v;
    }
"""
    new = ""
else:
    raise SystemExit("MUTANT must be 1, 2 or 3")
if old not in s:
    raise SystemExit(f"mutant {mutant}: source pattern not found")
open(p, "w").write(s.replace(old, new, 1))
PY
  echo "contract mutant $MUTANT: expecting the contract test to fail"
  mutant_cc="${CC:-gcc}"; set -- $mutant_cc; mutant_cc="$1"
  "$mutant_cc" $base_cflags $opt_cflags -o "$out/ct.mutant" \
    tests/contract/contract_test.c "$adapter" c/src/matching_engine_gen.c
  if "$out/ct.mutant" 1 1 300 5; then
    echo "contract mutant $MUTANT NOT caught"; exit 1
  else
    echo "contract mutant $MUTANT caught"; exit 0
  fi
fi
for cc in $ccs; do
  $cc $base_cflags $opt_cflags -o "$out/ct.$cc" \
    tests/contract/contract_test.c "$adapter" c/src/matching_engine_gen.c
  for cap in 0 1 2 5 16 64; do
    echo "[$cc]"; "$out/ct.$cc" "$first" "$seeds" "$ops" "$cap"
  done
done
