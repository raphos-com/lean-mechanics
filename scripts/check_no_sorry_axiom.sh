#!/usr/bin/env bash
# Fails if the library contains `sorry`, `admit`, or an `axiom` declaration,
# or if any declaration of the library depends on an axiom other than
# Lean's three standard ones (propext, Classical.choice, Quot.sound).
# Usage: scripts/check_no_sorry_axiom.sh   (run from the repository root, after `lake build`)
set -euo pipefail

status=0

# 1. Source scan (comments are not stripped: a `sorry` in a comment is also rejected,
#    which keeps the check simple; write "s0rry" in prose if ever needed).
if grep -rnwE 'sorry|admit' --include='*.lean' ContinuumMechanics ContinuumMechanics.lean; then
  echo "error: found sorry/admit (listed above)" >&2
  status=1
fi
if grep -rnE '^\s*(private\s+|protected\s+)?axiom\s' --include='*.lean' ContinuumMechanics ContinuumMechanics.lean; then
  echo "error: found axiom declarations (listed above)" >&2
  status=1
fi

# 2. Semantic check: every declaration in the library uses only the standard axioms.
tmp=$(mktemp --suffix=.lean)
trap 'rm -f "$tmp"' EXIT
cat > "$tmp" <<'LEAN'
import ContinuumMechanics
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  for (n, _) in env.constants.toList do
    if (`ContinuumMechanics).isPrefixOf n then
      for ax in (← Lean.collectAxioms n) do
        unless allowed.contains ax do bad := bad.push (n, ax)
  if bad.isEmpty then
    IO.println "axiom check: ok"
  else
    for (n, ax) in bad do IO.eprintln s!"{n} depends on {ax}"
    throwError "non-standard axioms found"
LEAN
if ! lake env lean "$tmp"; then
  status=1
fi

exit $status
