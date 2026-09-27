#!/usr/bin/env bash
# Phase 3 evidence: the generated matcher (c/gen/matcher.c + adapter + handwritten
# data layer) and the handwritten engine produce identical traces — return value,
# trades, book after every call, invariant check — on seeded random streams.
# Usage: scripts/matcher_c_diff.sh [first_seed] [seeds] [steps]
set -euo pipefail
cd "$(dirname "$0")/.."
first="${1:-1}"; seeds="${2:-50}"; steps="${3:-400}"
out="$(mktemp -d)"; trap 'rm -rf "$out"' EXIT
make -s bin/gen_matcher.o bin/gen_adapter.o bin/gen_glue.o bin/gen_hw_engine.o bin/gen_data_layer.o
cc -O2 -Wall -Wextra -Werror -Ic/include -o "$out/hw" c/tests/diff_driver.c c/src/matching_engine.c c/src/matching_engine_gen.c
cc -O2 -Wall -Wextra -Werror -Ic/include -Ic/gen -o "$out/gen" c/tests/diff_driver.c \
  bin/gen_matcher.o bin/gen_adapter.o bin/gen_glue.o bin/gen_hw_engine.o bin/gen_data_layer.o
fail=0
for ((s = first; s < first + seeds; s++)); do
  "$out/hw" "$s" "$steps" > "$out/hw.txt"
  "$out/gen" "$s" "$steps" > "$out/gen.txt"
  if ! cmp -s "$out/hw.txt" "$out/gen.txt"; then
    echo "seed $s: traces differ"; diff "$out/hw.txt" "$out/gen.txt" | head -20; fail=1; break
  fi
  if grep -q "inv=0" "$out/gen.txt"; then echo "seed $s: invariant check failed"; fail=1; break; fi
done
calls=$((seeds * steps))
[ "$fail" = 0 ] && echo "c differential: $seeds seeds x $steps calls = $calls calls, traces identical, invariants hold"
exit "$fail"
