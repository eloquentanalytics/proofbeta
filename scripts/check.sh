#!/usr/bin/env bash
# Copyright (c) 2026 the proofbeta authors. All rights reserved. See LICENSE.
# The checks. Every step must pass; the first failure stops the run. Needs elan's `lake` (on PATH or in
# ~/.elan/bin) and python3 (step 3 only, standard library).
#
#   1. build: the model, the theorems, the worked examples (#guard), the JSON round trips and the three engines,
#      stamped first with the revision they are built from (scripts/stamp_revision); no warning, no sorry
#   2. axioms: every declaration under StreamCore and Work depends on propext, Quot.sound and Classical.choice at
#      most (scripts/Axioms.lean)
#   3. forbidden words in the Lean sources, comments and strings stripped: no sorry, admit, axiom, partial, unsafe,
#      implemented_by, extern or native_decide; and the work layer imports nothing of the core but its interface
#   4. audit of the decision functions' dependency tree (scripts/Audit.lean)
#   5. the engines' self-tests: the worked examples through the compiled code
#   6. every gap stated in StreamCore/Theorems.lean has a row in the README, and every row a statement
#   7. the corpus: every recorded session replays byte for byte (corpus/replay)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LAKE="${LAKE:-$(command -v lake || echo "$HOME/.elan/bin/lake")}"
PY="${PYTHON:-python3}"
cd "$ROOT"
step() { printf '\n== %s\n' "$*"; }

# The Lean sources the forbidden-word scan reads: every .lean file of the package (the libraries and the engines'
# roots), not the generated EngineRevision.lean and not the check scripts under scripts/ (Audit.lean uses `partial`).
sources() { find StreamCore Engine Work -name '*.lean' | sort; ls ./*.lean | grep -v '^./EngineRevision.lean$'; }

step "1. lake build"
"$ROOT/scripts/stamp_revision"
out="$("$LAKE" build 2>&1)" || { echo "$out"; exit 1; }
if grep -qE "warning|declaration uses 'sorry'" <<<"$out"; then echo "$out" | grep -A3 -E "warning|sorry"; exit 1; fi
echo "$out" | tail -1

step "2. axioms (allowed: propext, Quot.sound, Classical.choice)"
ax="$("$LAKE" env lean scripts/Axioms.lean 2>&1)" || { echo "$ax"; exit 1; }
echo "$ax"
[[ "$(grep -c '^axioms: .*at most$' <<<"$ax")" == 2 ]] || exit 1

step "3. forbidden words in the Lean sources (comments and strings stripped)"
files="$(sources)"
[[ "$(wc -l <<<"$files" | tr -d ' ')" -ge 25 ]] || { echo "the scan found too few sources: $files"; exit 1; }
# shellcheck disable=SC2086
hits=$("$PY" scripts/strip_lean_comments.py $files \
  | grep -wE "sorry|admit|axiom|partial|unsafe|implemented_by|extern|native_decide" || true)
if [[ -n "$hits" ]]; then echo "$hits"; exit 1; fi
echo "$(wc -l <<<"$files" | tr -d ' ') files: none"
bad=$(grep -hE "^import " Work/*.lean | grep -vE "^import (StreamCore\.Interface|Work\.)" || true)
[[ -z "$bad" ]] || { echo "Work imports more of the core than its interface: $bad"; exit 1; }
echo "Work/*.lean imports the core's interface only"

step "4. audit of the decision functions' dependency tree"
"$LAKE" env lean scripts/Audit.lean 2>&1 | grep -E "^audit" || { "$LAKE" env lean scripts/Audit.lean; exit 1; }

step "5. engine self-tests (compiled code)"
.lake/build/bin/stream-engine --self-test
.lake/build/bin/work-engine --self-test
.lake/build/bin/work-engine --revision

step "6. every gap stated in StreamCore/Theorems.lean has a row in the README, and every row a statement"
gaps=$(grep -oE '^- \*\*gap_[a-z_]+\.' StreamCore/Theorems.lean | grep -oE 'gap_[a-z_]+')
for g in $gaps; do grep -qE "^\| $g \|" README.md || { echo "$g: not in the README table"; exit 1; }; done
for g in $(grep -oE '^\| gap_[a-z_]+ \|' README.md | grep -oE 'gap_[a-z_]+'); do
  grep -qE "^- \*\*$g\." StreamCore/Theorems.lean || { echo "README $g: not stated in Theorems.lean"; exit 1; }
done
echo "$(wc -w <<<"$gaps" | tr -d ' ') gaps, each stated in Theorems.lean and tabled in the README"

step "7. corpus replay"
corpus/replay

printf '\ncheck.sh: all passed\n'
