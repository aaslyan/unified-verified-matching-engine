#!/usr/bin/env bash
# Differential test (plan v2 Phase 5, item 2). For each seed, a random request
# stream (gen_stream.py) is run through
#   - the executable spec, processB (lean/Matcher/Oracle.lean, `spec_oracle`): the oracle;
#   - the generated matcher + adapter + handwritten data layer (runner.c -DRUN_GEN);
#   - the handwritten engine (runner.c -DRUN_HW): a third voice.
# Oracle and generated matcher must agree on every step's Obs (result code,
# trades, book view). The handwritten engine is compared up to its first
# divergence, which is classified by the oracle's result code at that step
# (capacity = 5, invalid = 3, ...) and recorded per seed; it does not fail the run.
# Usage: tests/differential/run.sh [first_seed] [seeds] [length] [capacity] [full|noqmax]
set -euo pipefail
cd "$(dirname "$0")/../.."
first="${1:-1}"; seeds="${2:-20}"; len="${3:-300}"; cap="${4:-8}"; profile="${5:-full}"
out="$(mktemp -d)"; trap 'rm -rf "$out"' EXIT
lake build spec_oracle >/dev/null
cc="${CC:-cc}"
CF="-std=c11 -Wall -Wextra -Werror -Ic/gen -Ic/include ${CFLAGS:--O2}"
"$cc" $CF -DRUN_GEN -o "$out/gen" tests/differential/runner.c c/gen/matcher.c c/gen/engine_db_adapter.c c/src/matching_engine_gen.c
"$cc" $CF -DRUN_HW -o "$out/hw" tests/differential/runner.c c/src/matching_engine.c c/src/matching_engine_gen.c
"$cc" $CF -o "$out/tov" tests/differential/total_overflow.c c/src/matching_engine.c c/src/matching_engine_gen.c
"$out/tov"   # the handwritten engine's latent level-total overflow (EVIDENCE.md §2)
steps=0; oracle_ns=0; fail=0
: > "$out/hwclass.txt"; : > "$out/cov.txt"
for ((s = first; s < first + seeds; s++)); do
  python3 tests/differential/gen_stream.py "$s" "$len" "$cap" "$profile" > "$out/stream.txt"
  t0=$(date +%s%N)
  .lake/build/bin/spec_oracle "$cap" "$out/stream.txt" > "$out/spec.txt"
  t1=$(date +%s%N)
  oracle_ns=$((oracle_ns + t1 - t0))
  "$out/gen" "$cap" "$out/stream.txt" > "$out/gen.txt"
  "$out/hw" "$cap" "$out/stream.txt" > "$out/hw.txt"
  steps=$((steps + len))
  if ! cmp -s "$out/spec.txt" "$out/gen.txt"; then
    echo "MISMATCH seed $s (oracle vs generated):"; diff "$out/spec.txt" "$out/gen.txt" | head -20
    fail=1
  fi
  python3 - "$out/spec.txt" "$out/stream.txt" "$cap" >> "$out/cov.txt" <<'PY'
import sys
steps, cur = [], None
for l in open(sys.argv[1]).read().splitlines():
    if not l.startswith("  "): cur = [l]; steps.append(cur)
    else: cur.append(l)
reqs = [l.split() for l in open(sys.argv[2]).read().splitlines() if l.strip()]
cap = int(sys.argv[3]); size = 0; po_full = 0
codes = [0] * 8
for k, st in enumerate(steps):
    code = int(st[0].split()[2]); codes[code] += 1
    if reqs[k][0] == "O" and reqs[k][4] == "3" and size >= cap: po_full += 1
    size = sum(len(l.split(":")[1].split()) for l in st[1:] if l.startswith("  bid") or l.startswith("  ask"))
print(" ".join(map(str, codes + [po_full])))
PY
  python3 - "$out/spec.txt" "$out/hw.txt" "$s" "$out/stream.txt" "$cap" >> "$out/hwclass.txt" <<'PY'
import sys, re
reqs = [l.split() for l in open(sys.argv[4]).read().splitlines() if l.strip()]
qmax = (2**64 - 1) // (int(sys.argv[5]) + 1)
def steps(path):
    out, cur = [], None
    for l in open(path).read().splitlines():
        if not l.startswith("  "):
            cur = [l]; out.append(cur)
        else:
            cur.append(l)
    return out
spec, hw = steps(sys.argv[1]), steps(sys.argv[2])
names = {0: "accepted", 1: "cancelled", 2: "unsupported", 3: "invalid", 4: "duplicate",
         5: "capacity", 6: "postOnly", 7: "unknownId"}
for k, (a, b) in enumerate(zip(spec, hw)):
    code = int(a[0].split()[2]); ok = int(b[0].split()[2])
    if (code in (0, 1)) != (ok == 1) or a[1:] != b[1:]:
        name = names[code]
        if code == 3 and reqs[k][0] == "O" and int(reqs[k][7]) > qmax:
            name = "invalid(qty>Qmax)"
        print(f"{sys.argv[3]} {k} {name}"); break
else:
    print(f"{sys.argv[3]} - identical")
PY
done
python3 - "$out/cov.txt" <<'PY'
import sys
rows = [list(map(int, l.split())) for l in open(sys.argv[1]).read().splitlines()]
tot = [sum(c) for c in zip(*rows)]
names = ["accepted", "cancelled", "unsupported", "invalid", "duplicate", "capacity", "postOnly", "unknownId"]
print("  oracle result codes: " + ", ".join(f"{n} {v}" for n, v in zip(names, tot[:8])) +
      f"; post-only requests at a full store: {tot[8]}")
PY
python3 - "$out/hwclass.txt" "$seeds" "$len" "$cap" "$steps" "$oracle_ns" "$profile" <<'PY'
import sys, collections
rows = [l.split() for l in open(sys.argv[1]).read().splitlines()]
seeds, length, cap, steps, ns = map(int, sys.argv[2:7])
cls = collections.Counter(r[2] if r[1] != "-" else "identical" for r in rows)
print(f"differential (cap {cap}, profile {sys.argv[7]}): {seeds} seeds x {length} requests = {steps} steps; "
      f"oracle vs generated: see above (MISMATCH lines) / agreement checked on every step")
print(f"  oracle throughput: {steps / (ns / 1e9):.0f} requests/s")
print(f"  handwritten engine, first divergence class per seed: {dict(cls)}")
print("  per seed: " + " ".join(f"{r[0]}:{r[2] if r[1] != '-' else 'identical'}@{r[1]}" for r in rows))
PY
if [ $fail = 0 ]; then echo "differential: oracle and generated matcher agree on all $steps steps"; fi
exit $fail
