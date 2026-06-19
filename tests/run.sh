#!/usr/bin/env bash
# Runs each test file through `lake env lean`. A file "passes" if Lean reports no
# errors (failed `#guard` / `#guard_msgs` / `throwError` in `#eval` all surface as
# errors and make `lean` exit non-zero). Exits non-zero if any file fails.
#
# Until `src/` implements the contract the tests target, the suite is expected to be
# RED (that is the point of TDD) — but every expected value has been independently
# verified to be mathematically correct.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

files=(
  tests/Unit/Digraph.lean
  tests/Unit/Condensation.lean
  tests/Unit/ClassApp.lean
  tests/Behavior/Weakening.lean
  tests/Behavior/CrossFrameRendering.lean
)

fail=0
for f in "${files[@]}"; do
  printf '▶ %s\n' "$f"
  if lake env lean "$f"; then
    printf '  ✓ pass\n'
  else
    printf '  ✗ FAIL\n'
    fail=1
  fi
done
exit "$fail"
