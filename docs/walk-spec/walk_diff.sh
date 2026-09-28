#!/usr/bin/env bash
# Walk-spec A1 differentials (see lean/Walk/Check.lean):
#   D1  Walk.process vs processB (obsSpec)
#   D2  matcher under execStmt on the model store vs Walk.process
# Phase 3 streams (MatcherCheck.genReq, seed 7, 400 x 60) at capacities 2, 6, 20
# plus 1; fill streams (genFill, seed 11, 200 x 60) at capacities 1, 2, 6, 20.
# Any mismatch or trap fails.
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build Walk.Check >/dev/null
run() { WALK_GEN=$1 WALK_SEED=$2 WALK_STREAMS=$3 WALK_LEN=$4 WALK_CAP=$5 \
  lake env lean lean/Walk/CheckRun.lean; }
for cap in 2 6 20 1; do run rand 7 400 60 "$cap"; done
for cap in 1 2 6 20; do run fill 11 200 60 "$cap"; done
