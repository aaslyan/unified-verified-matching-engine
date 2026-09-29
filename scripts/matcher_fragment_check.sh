#!/usr/bin/env bash
# Phase 2 acceptance: print the fragment check program (lean/Matcher/Example.lean)
# and compile it under gcc and clang with -std=c11 -Wall -Wextra -Werror.
# Compile only (-c): the data layer behind c/gen/engine_db.h is linked in Phase 3.
set -euo pipefail
cd "$(dirname "$0")/.."
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
lake build Matcher.Example >/dev/null
lake env lean --run lean/Matcher/Example.lean > "$out/fragment_example.c"
for cc in gcc clang; do
  if command -v "$cc" >/dev/null; then
    for opt in -O0 -O2; do
      "$cc" -std=c11 -Wall -Wextra -Werror "$opt" -Ic/gen -c "$out/fragment_example.c" \
        -o "$out/fragment_example_${cc}_${opt#-}.o"
      echo "fragment check: $cc $opt OK"
    done
  else
    echo "fragment check: $cc not found" >&2
    exit 1
  fi
done
