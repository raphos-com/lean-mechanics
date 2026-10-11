#!/usr/bin/env bash
# Build the API documentation of this repository's modules only (not of Mathlib or Lean core).
#
# doc-gen4's Lake facets (`Lib:docs`) first document every imported module, i.e. most of Mathlib.
# Instead we call the doc-gen4 executable directly: `single` adds one of our modules to the
# documentation database, `fromDb` renders the HTML. Links to imported Mathlib/Lean modules are
# redirected to the official Mathlib documentation.
#
# Usage (from the repository root, after `lake build`, `(cd papers && lake build)` and
# `(cd docbuild && lake build doc-gen4)`):
#   scripts/build_docs.sh [output-dir]      (default: docbuild/.lake/build)
set -euo pipefail

# Run everything inside a single `lake env` (one Lean search path for all modules).
if [ -z "${LAKE_ENV_DONE:-}" ]; then
  # The papers project depends on both libraries, so its environment sees every module.
  LAKE_ENV_DONE=1 exec lake --dir papers env "$0" "$@"
fi

exe=".lake/packages/doc-gen4/.lake/build/bin/doc-gen4"
build="${1:-docbuild/.lake/build}"
rev="$(git rev-parse HEAD)"
base="https://github.com/raphos-com/lean-mechanics/blob/${rev}"
upstream="https://leanprover-community.github.io/mathlib4_docs"

rm -rf "$build/doc" "$build/api-docs.db"
mkdir -p "$build"

# Library roots: ContinuumMechanics, DiscreteMechanics (in ./) and the paper libraries (in ./papers).
roots=(ContinuumMechanics DiscreteMechanics)
for f in papers/*.lean; do roots+=("$(basename "$f" .lean)"); done

# Paper libraries used to be built by the root package; stale outputs of theirs in the root build
# directory (e.g. restored from a CI cache) would shadow the current ones in `papers/.lake`.
for r in "${roots[@]:2}"; do
  rm -rf ".lake/build/lib/lean/$r" .lake/build/lib/lean/"$r".* ".lake/build/ir/$r" .lake/build/ir/"$r".*
done

# Every module of the repository, with its source path.
mapfile -t files < <( { find ContinuumMechanics DiscreteMechanics -name '*.lean';
  echo ContinuumMechanics.lean; echo DiscreteMechanics.lean;
  find papers -name '*.lean' -not -path '*/.lake/*'; } | sort )

for f in "${files[@]}"; do
  rel="${f#papers/}"
  mod="${rel%.lean}"; mod="${mod//\//.}"
  "$exe" single --build "$build" "$mod" api-docs.db "$base/$f" >/dev/null
done

"$exe" fromDb --build "$build" --manifest "$build/doc-manifest.json" \
  "$build/api-docs.db" "${roots[@]}"

# Point links to imported upstream modules at the official documentation and drop the local stubs.
doc="$build/doc"
upstreamRoots="Mathlib|Init|Lean|Std|Lake|Batteries|Aesop|Qq|ProofWidgets|Plausible|ImportGraph|LeanSearchClient"
find "$doc" -name '*.html' -print0 | xargs -0 sed -i -E \
  "s#href=\"(\.\./)*\./(${upstreamRoots//|/|})([/.])#href=\"${upstream}/\2\3#g"
for r in ${upstreamRoots//|/ }; do rm -rf "${doc:?}/$r" "$doc/$r.html"; done
echo "documentation: $doc ($(find "$doc" -name '*.html' | wc -l) pages)"
