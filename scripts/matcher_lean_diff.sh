#!/usr/bin/env bash
# Regression check (plan v2, through Phase 4): the matcher program under the
# Lean semantics on the model store against processB, on seeded random streams,
# at capacities 2, 6 and 20. Any mismatch fails.
# Usage: scripts/matcher_lean_diff.sh [seed] [streams] [length]
set -euo pipefail
cd "$(dirname "$0")/.."
seed="${1:-7}"; streams="${2:-400}"; len="${3:-60}"
lake build Matcher.CheckLean >/dev/null
for cap in 2 6 20; do
  lake env lean --run lean/Matcher/CheckLean.lean "$seed" "$streams" "$len" "$cap"
done
