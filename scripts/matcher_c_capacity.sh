#!/usr/bin/env bash
# Phase 4 pre-check: the C differential with a small capacity, so the store
# fills. The generated matcher applies the v2 capacity rule (reject a request
# that may rest when the store is full, before any trade); the handwritten
# engine has no such rule (its pools hold millions of rows). So the traces are
# expected to diverge, and every first divergence must be of that class:
# an order of type LIMIT (0) or POST_ONLY (3), store at capacity, generated
# returns 0, handwritten returns 1. Anything else fails.
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
diverged=0; identical=0
for ((s = first; s < first + seeds; s++)); do
  "$out/hw" "$s" "$steps" > "$out/hw.txt"
  "$out/gen" "$s" "$steps" > "$out/gen.txt"
  if grep -q "inv=0" "$out/gen.txt"; then echo "seed $s: invariant check failed (generated)"; exit 1; fi
  if cmp -s "$out/hw.txt" "$out/gen.txt"; then identical=$((identical + 1)); continue; fi
  python3 - "$out/hw.txt" "$out/gen.txt" "$cap" "$s" <<'PY'
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
hw, gen = blocks(sys.argv[1]), blocks(sys.argv[2])
cap, seed = int(sys.argv[3]), sys.argv[4]
k = next(i for i in range(min(len(hw), len(gen))) if hw[i] != gen[i])
def result(b):
    for l in b["lines"]:
        m = re.search(r"order id=\d+ .*type=(\d+) .* -> (\d)$", l)
        if m: return int(m.group(1)), m.group(2)
    return None
g, h = result(gen[k]), result(hw[k])
gtrades = [l for l in gen[k]["lines"] if "trade" in l]
ok = (g is not None and h is not None and g[0] in (0, 3) and g[1] == "0" and h[1] == "1"
      and gen[k]["pool"] >= cap and not gtrades)
if not ok:
    print(f"seed {seed}: unexpected first divergence at request {k} (pool {gen[k]['pool']}):")
    print("  hw :", *hw[k]["lines"][:4], sep="\n    ")
    print("  gen:", *gen[k]["lines"][:4], sep="\n    ")
    sys.exit(1)
PY
  diverged=$((diverged + 1))
done
echo "c capacity differential (cap $cap): $seeds seeds x $steps calls; $identical identical, $diverged diverged, every divergence at capacity (expected: generated rejects before trading, handwritten rests)"
