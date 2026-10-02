#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# The whole proof gate, in the order CI runs it:
#   1. axiom audit (postulates, FFI, unsound flags, holes, reachability)
#   2. type-check ExactCounts/All.agda; any Agda warning is a failure
#   3. reject controls: every false statement in agda/reject/ must fail
#   4. gate self-test: deliberate breakages must each be rejected
#   5. vector extraction is up to date (needs bun; refused, not skipped, if absent)
#
# Usage: proofs/check.sh

set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/lib.sh"
resolve_agda
resolve_stdlib
printf 'check: %s, %s\n' "$("$AGDA" --version)" "$STDLIB_PINNED_NAME"

"$PROOFS_DIR/tests/axiom-audit.sh"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
write_libraries "$WORK/libraries" "$AGDA_DIR"
( cd "$AGDA_DIR" && "$AGDA" --library-file="$WORK/libraries" ExactCounts/All.agda ) 2>&1 | tee "$WORK/typecheck.log"
if grep -qiE '^warning|^[^ ].*: *warning' "$WORK/typecheck.log"; then
  die "Agda emitted warnings"
fi
printf 'check: ExactCounts/All.agda type-checks\n'

"$PROOFS_DIR/tests/reject-controls.sh"
"$PROOFS_DIR/tests/gate-selftest.sh"

command -v bun >/dev/null 2>&1 || die "bun not found: the vectors cannot be re-extracted, so their freshness is unchecked"
bun "$PROOFS_DIR/extract-vectors.js" --check
