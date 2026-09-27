#!/usr/bin/env bash
# Phase 4 pre-check: the C differential with a small capacity, so the store
# fills. The generated matcher applies the v2 capacity rule (reject a request
# that may rest when the store is full, before any trade); the handwritten
# engine has no such rule (its pools hold millions of rows). The public API
# reports only accepted/rejected (a bool), so result codes are not compared,
# only that bool, the trades and the books.
#
# Two cases at a full store, described separately:
#  * POST_ONLY that would cross: the handwritten engine rejects it (post-only
#    rule), the generated matcher rejects it (capacity rule). Different codes
#    inside, same bool, both books unchanged: the call agrees, the seed goes on.
#  * LIMIT, or POST_ONLY that would not cross: the handwritten engine rests it
#    (bool 1), the generated matcher rejects it (bool 0) before any trade. The
#    books now differ: the seed ends at this call (first state divergence).
# Every first state divergence must be of the second kind; anything else fails.
# The report gives the mean number of calls compared per seed before it.
# Usage: scripts/matcher_c_capacity.sh [capacity] [first_seed] [seeds] [steps]
set -euo pipefail
cd "$(dirname "$0")/.."
cap="${1:-8}"; first="${2:-1}"; seeds="${3:-50}"; steps="${4:-300}"
out="$(mktemp -d)"; trap 'rm -rf "$out"' EXIT
CF="-O2 -Wall -Wextra -Werror -Ic/include -Ic/gen"
HWR="-DMatchingEngine_Init=hw_MatchingEngine_Init -DMatchingEngine_ProcessOrder=hw_MatchingEngine_ProcessOrder -DMatchingEngine_CancelOrder=hw_MatchingEngine_CancelOrder"
cc $CF -o "$out/hw" c/tests/diff_driver.c c/src/matching_engine.c c/src/matching_engine_gen.c
cc $CF -std=c11 -c -o "$out/m.o" c/gen/matcher.c
cc $CF -c -o "$out/a.o" c/gen/engine_db_adapter.c
cc $CF -DME_GLUE_CAPACITY="UINT64_C($cap)" -c -o "$out/g.o" c/gen/matcher_glue.c
cc $CF $HWR -c -o "$out/h.o" c/src/matching_engine.c
cc $CF -o "$out/gen" c/tests/diff_driver.c "$out/m.o" "$out/a.o" "$out/g.o" "$out/h.o" c/src/matching_engine_gen.c
: > "$out/stats.txt"
for ((s = first; s < first + seeds; s++)); do
  "$out/hw" "$s" "$steps" > "$out/hw.txt"
  "$out/gen" "$s" "$steps" > "$out/gen.txt"
  if grep -q "inv=0" "$out/gen.txt"; then echo "seed $s: invariant check failed (generated)"; exit 1; fi
  python3 - "$out/hw.txt" "$out/gen.txt" "$cap" "$s" >> "$out/stats.txt" <<'PY'
import sys, re
def blocks(path):
    out, cur = [], None
    for line in open(path).read().splitlines():
        m = re.match(r"\d+ pool=(\d+)$", line)
        if m:
            cur = {"pool": int(m.group(1)), "lines": []}; out.append(cur)
        elif cur is not None:
            cur["lines"].append(line)
    return out
def result(b):
    for l in b["lines"]:
        m = re.search(r"order id=\d+ .*type=(\d+) .* -> (\d)$", l)
        if m: return int(m.group(1)), m.group(2)
    return None
hw, gen = blocks(sys.argv[1]), blocks(sys.argv[2])
cap, seed = int(sys.argv[3]), sys.argv[4]
n = min(len(hw), len(gen))
k = next((i for i in range(n) if hw[i] != gen[i]), n)
# POST_ONLY at a full store before the divergence: both reject, same books
po_agree = sum(1 for i in range(k) if gen[i]["pool"] >= cap and (result(gen[i]) or (None,))[0] == 3
               and result(gen[i])[1] == "0")
if k == n:
    print(f"identical {k} {po_agree} -"); sys.exit(0)
g, h = result(gen[k]), result(hw[k])
gtrades = [l for l in gen[k]["lines"] if "trade" in l]
ok = (g is not None and h is not None and g[0] in (0, 3) and g[1] == "0" and h[1] == "1"
      and gen[k]["pool"] >= cap and not gtrades)
if not ok:
    print(f"seed {seed}: unexpected first divergence at request {k} (pool {gen[k]['pool']}):", file=sys.stderr)
    print("  hw :", *hw[k]["lines"][:4], sep="\n    ", file=sys.stderr)
    print("  gen:", *gen[k]["lines"][:4], sep="\n    ", file=sys.stderr)
    sys.exit(1)
print(f"diverged {k} {po_agree} {'LIMIT' if g[0] == 0 else 'POST_ONLY'}")
PY
done
python3 - "$out/stats.txt" "$cap" "$seeds" "$steps" <<'PY'
import sys
rows = [l.split() for l in open(sys.argv[1]).read().splitlines()]
cap, seeds, steps = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
ident = [r for r in rows if r[0] == "identical"]
div = [r for r in rows if r[0] == "diverged"]
mean = sum(int(r[1]) for r in rows) / len(rows)
po = sum(int(r[2]) for r in rows)
lim = sum(1 for r in div if r[3] == "LIMIT"); pon = len(div) - lim
print(f"c capacity differential (cap {cap}): {seeds} seeds x {steps} calls; "
      f"{len(ident)} identical to the end, {len(div)} ended at a state divergence "
      f"({lim} LIMIT, {pon} non-crossing POST_ONLY rested by the handwritten engine, "
      f"rejected for capacity by the generated one)")
print(f"  mean calls compared per seed before the first state divergence: {mean:.1f}")
print(f"  POST_ONLY at a full store rejected by both (post-only vs capacity, same books) "
      f"and continued: {po}")
PY
