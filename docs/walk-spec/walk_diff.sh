#!/usr/bin/env bash
# Walk-spec A1 differentials (see lean/Walk/Check.lean):
#   D1  Walk.process vs processB (obsSpec)
#   D2  matcher under execStmt on the model store vs Walk.process
# Phase 3 streams (MatcherCheck.genReq, seed 7, 400 x 60) at capacities 2, 6, 20
# plus 1; fill streams (genFill, seed 11, 200 x 60) at capacities 1, 2, 6, 20.
# Any mismatch or trap fails.
#
# MUTANT=1|2: harness self-check. Plants a known wrong transliteration in
# lean/Walk/Spec.lean, runs genReq seed 7, 40 x 60, cap 6, and succeeds only if
# the differential FAILS; Spec.lean is restored on exit.
#   1  CANCEL_BOTH does not zero rem (C:121-122; innerStep, the stpMode = 3 case)
#   2  the level cleanup never fires (C:156; outerStep, `levelCount best' = 0`)
set -euo pipefail
cd "$(dirname "$0")/../.."
run() { WALK_GEN=$1 WALK_SEED=$2 WALK_STREAMS=$3 WALK_LEN=$4 WALK_CAP=$5 \
  lake env lean docs/walk-spec/CheckRun.lean; }

if [ -n "${MUTANT:-}" ]; then
  spec=lean/Walk/Spec.lean
  case "$MUTANT" in
    1) pat='if c.r.stpMode = 3 then some { st with book := b1, rem := 0 }'
       rep='if c.r.stpMode = 3 then some { st with book := b1 }' ;;
    2) pat="if levelCount best' = 0 then some"
       rep="if levelCount best' = 7 then some" ;;
    *) echo "MUTANT must be 1 or 2"; exit 2 ;;
  esac
  git diff --quiet -- "$spec" || { echo "$spec has local changes; refusing"; exit 2; }
  line=$(grep -nF "$pat" "$spec" | cut -d: -f1)
  [ -n "$line" ] || { echo "mutant $MUTANT: pattern not found"; exit 2; }
  trap 'git checkout -q -- "$spec"; lake build Walk.Check >/dev/null' EXIT
  python3 - "$spec" "$pat" "$rep" <<'PY'
import sys; p, a, b = sys.argv[1:]
s = open(p).read(); open(p, 'w').write(s.replace(a, b, 1))
PY
  echo "mutant $MUTANT: $spec line $line"
  lake build Walk.Check >/dev/null
  if run rand 7 40 60 6; then echo "mutant $MUTANT NOT caught"; exit 1
  else echo "mutant $MUTANT caught"; exit 0; fi
fi

lake build Walk.Check >/dev/null
for cap in 2 6 20 1; do run rand 7 400 60 "$cap"; done
for cap in 1 2 6 20; do run fill 11 200 60 "$cap"; done
