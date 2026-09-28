#!/usr/bin/env bash
# All Phase 5 suites at the scale recorded in docs/plan-v2/EVIDENCE.md.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== printer"; tests/printer/run.sh
echo "== contract"; tests/contract/run.sh 1 50 3000
echo "== differential"
for cap in 2 8 64 1000000; do tests/differential/run.sh 1 100 300 "$cap"; done
echo "== semantics"
for cap in 0 1 3 7; do for seed in 1 2 3 4 5; do tests/semantics/run.sh "$seed" 200 "$cap"; done; done
