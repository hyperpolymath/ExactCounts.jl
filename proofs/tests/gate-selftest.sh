#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Prove that the proof gate can fail.
#
# A gate that has never been observed to reject anything is not evidence.  This
# script takes a throwaway copy of the proof tree, breaks it in one specific way
# at a time, and requires the gate to reject it.  If any mutation is *accepted*,
# or if a mutation failed to apply at all, this script exits non-zero.  There is
# no flag to turn it off.
#
# Usage: proofs/tests/gate-selftest.sh

set -uo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/../lib.sh"
resolve_agda
resolve_stdlib

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
cp -r "$AGDA_DIR" "$WORK/agda"
cp -r "$PROOFS_DIR/tests" "$WORK/tests"
cp "$PROOFS_DIR/lib.sh" "$WORK/lib.sh"
rm -rf "$WORK/agda/_build"

# Point Agda at the *copy*: otherwise the library file would resolve
# `ExactCounts.All` back to the pristine tree and every mutation below would be
# checked against unmutated sources, a self-test that tests nothing.
write_libraries "$WORK/libraries" "$WORK/agda"

# Type-check the copied tree's gate entry point.
run_gate() {
  ( cd "$WORK/agda" && "$AGDA" --library-file="$WORK/libraries" ExactCounts/All.agda ) \
    >"$WORK/out.txt" 2>&1
}
# Run the copied axiom audit against the copied tree.
run_audit() { "$WORK/tests/axiom-audit.sh" >"$WORK/out.txt" 2>&1; }

total=0
failed=0

# Apply one mutation to one file of the copy, require the runner to reject the
# result, then restore the file.  Usage: expect_reject <name> <runner> <file> <mutator>
expect_reject() {
  local name="$1" runner="$2" target="$3" mutator="$4"
  local file="$WORK/agda/$target"
  total=$((total + 1))

  cp "$AGDA_DIR/$target" "$file"
  local before after
  before="$(sha256sum "$file" | awk '{print $1}')"
  bash -c "$mutator" mutator "$file"
  after="$(sha256sum "$file" | awk '{print $1}')"
  if [[ "$before" == "$after" ]]; then
    printf 'gate-selftest: FAIL  %-46s mutation did not apply (stale pattern?)\n' "$name"
    failed=$((failed + 1))
    return
  fi

  if $runner; then
    printf 'gate-selftest: FAIL  %-46s gate ACCEPTED a broken proof\n' "$name"
    sed 's/^/                     | /' "$WORK/out.txt" | head -6
    failed=$((failed + 1))
  else
    printf 'gate-selftest: ok    %-46s rejected\n' "$name"
  fi
  cp "$AGDA_DIR/$target" "$file"
}

# --- the type-checker must reject wrong mathematics -------------------------

expect_reject "rounding: wrong known-answer digit" run_gate "ExactCounts/DecimalRounding.agda" \
  'sed -i "s|+ 402 ℤ.<? + 403|+ 402 ℤ.<? + 402|" "$1"'

expect_reject "rounding: tie forced the wrong way" run_gate "ExactCounts/DecimalRounding.agda" \
  'sed -i "s|half-ties-round-up : IsRoundHalfUp (+ 1) 1 0 (+ 1)|half-ties-round-up : IsRoundHalfUp (+ 1) 1 0 (+ 0)|" "$1"'

expect_reject "existence: negative witness not mirrored" run_gate "ExactCounts/DecimalRounding.agda" \
  'sed -i "s#^\.\.\. | m , p = - m ,#... | m , p = m ,#" "$1"'

expect_reject "existence: computed digit wrong" run_gate "ExactCounts/DecimalRounding.agda" \
  'sed -i "s|roundHalfAway (+ 2) 2 2 ≡ + 67|roundHalfAway (+ 2) 2 2 ≡ + 66|" "$1"'

expect_reject "proportions: zero total silently zero" run_gate "ExactCounts/Proportions.agda" \
  'sed -i "s#^\.\.\. | yes _ = refused zeroTotal#... | yes _ = value 0ℚᵘ#" "$1"'

# The general theorems survive this one (they are stated over any bound); only
# the 64-bit known-answer vectors catch it, which is what shows they bind.
expect_reject "exact counts: 2^63 admitted to Int64" run_gate "ExactCounts/Counts.agda" \
  'sed -i -e "s|(v < pow2 k)|(v ≤ pow2 k)|" -e "s|with v <? pow2 k|with v ≤? pow2 k|" "$1"'

expect_reject "vectors: wrong abundance" run_gate "ExactCounts/Vectors.agda" \
  'sed -i "s|relativeAbundance 2 3 ≡ value (mkℚᵘ (+ 2) 2)|relativeAbundance 2 3 ≡ value (mkℚᵘ (+ 1) 2)|" "$1"'

# --- the axiom audit must reject an unchecked or unsound module -------------

expect_reject "audit: module dropped from the gate entry" run_audit "ExactCounts/All.agda" \
  'sed -i "/import ExactCounts.Vectors/d" "$1"'

expect_reject "audit: postulate injected" run_audit "ExactCounts/DecimalRounding.agda" \
  'printf "postulate cheat : ∀ {A : Set} → A\n" >> "$1"'

expect_reject "audit: --safe removed" run_audit "ExactCounts/Proportions.agda" \
  'sed -i "s|--without-K --safe|--without-K|" "$1"'

# --- the gate must still accept the pristine tree --------------------------

total=$((total + 1))
if run_gate && run_audit; then
  printf 'gate-selftest: ok    %-46s accepted\n' "pristine tree"
else
  printf 'gate-selftest: FAIL  %-46s gate REJECTED the real proofs\n' "pristine tree"
  sed 's/^/                     | /' "$WORK/out.txt" | head -12
  failed=$((failed + 1))
fi

printf 'gate-selftest: %d/%d controls behaved correctly\n' "$((total - failed))" "$total"
[[ $failed -eq 0 ]]
