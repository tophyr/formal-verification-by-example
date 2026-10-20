#!/usr/bin/env bash
# Every check in the project, in order of strength. Exits non-zero if any fails.
set -euo pipefail
cd "$(dirname "$0")/.."
lake=${LAKE:-$HOME/.elan/bin/lake}
step() { printf '\n== %s\n' "$1"; }

step "build: type-check spec + impl + proofs, run compile-time tests, link binary"
"$lake" build

step "proof audit: every theorem proved, standard axioms only (Lean kernel)"
"$lake" env lean scripts/Audit.lean

step "curl contract: real curl behaves as the shell and the fake curl assume"
test/curl-contract.sh

step "end-to-end: real binary, fake curl"
test/e2e.sh

step "differential: original Python vs this (informational; see docs/06)"
test/differential.sh
printf '\nall checks passed\n'
