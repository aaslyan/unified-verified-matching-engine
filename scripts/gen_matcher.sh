#!/usr/bin/env bash
# Print the generated matcher (lean/Matcher/Program.lean) to c/gen/matcher.c.
# With --check, fail if the committed file differs from a fresh print.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Matcher.Emit >/dev/null
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
lake env lean --run lean/Matcher/Emit.lean > "$tmp"
if [ "${1:-}" = "--check" ]; then
  diff -u c/gen/matcher.c "$tmp" && echo "gen_matcher: c/gen/matcher.c is up to date"
else
  cp "$tmp" c/gen/matcher.c && echo "gen_matcher: wrote c/gen/matcher.c"
fi
