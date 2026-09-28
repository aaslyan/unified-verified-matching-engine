#!/usr/bin/env bash
# Contract tests (plan v2 Phase 5, item 1): the EngineDb laws against the
# adapter + handwritten data layer as linked under the matcher, at several
# capacities, under gcc -O2 and clang -O2.
# Usage: tests/contract/run.sh [first_seed] [seeds] [ops]
set -euo pipefail
cd "$(dirname "$0")/../.."
first="${1:-1}"; seeds="${2:-50}"; ops="${3:-3000}"
out="$(mktemp -d)"; trap 'rm -rf "$out"' EXIT
for cc in gcc clang; do
  $cc -std=c11 -O2 -Wall -Wextra -Werror -Ic/gen -Ic/include -o "$out/ct.$cc" \
    tests/contract/contract_test.c c/gen/engine_db_adapter.c c/src/matching_engine_gen.c
  for cap in 0 1 2 5 16 64; do
    echo "[$cc]"; "$out/ct.$cc" "$first" "$seeds" "$ops" "$cap"
  done
done
