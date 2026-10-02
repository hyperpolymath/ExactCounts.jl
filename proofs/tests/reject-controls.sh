#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Every module in proofs/agda/reject/ states something false and must NOT
# type-check.  Each declares the error it must fail with on an `-- EXPECT:` line,
# so a module that fails for an unrelated reason (a typo, a renamed import) is
# reported as a broken control instead of being counted as a rejection.
#
# Usage: proofs/tests/reject-controls.sh

set -uo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/../lib.sh"
resolve_agda
resolve_stdlib

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
write_libraries "$WORK/libraries" "$AGDA_DIR"

mapfile -t REJECTS < <(find "$AGDA_DIR/reject" -name '*.agda' -type f | sort)
[[ ${#REJECTS[@]} -gt 0 ]] || die "no reject controls found under $AGDA_DIR/reject"

failed=0
for f in "${REJECTS[@]}"; do
  name="reject/$(basename "$f")"
  expect="$(sed -n 's/^-- EXPECT: //p' "$f" | head -1)"
  if [[ -z "$expect" ]]; then
    printf 'reject-controls: FAIL  %-32s has no -- EXPECT: line\n' "$name"
    failed=$((failed + 1)); continue
  fi
  if ( cd "$AGDA_DIR" && "$AGDA" --library-file="$WORK/libraries" "$f" ) >"$WORK/out.txt" 2>&1; then
    printf 'reject-controls: FAIL  %-32s TYPE-CHECKED: a false statement was accepted\n' "$name"
    failed=$((failed + 1))
  elif grep -qF -- "$expect" "$WORK/out.txt"; then
    printf 'reject-controls: ok    %-32s rejected with the expected error\n' "$name"
  else
    printf 'reject-controls: FAIL  %-32s rejected, but not with: %s\n' "$name" "$expect"
    grep -v '^ *Checking' "$WORK/out.txt" | head -6 | sed 's/^/                       | /'
    failed=$((failed + 1))
  fi
done

printf 'reject-controls: %d/%d controls behaved correctly\n' "$((${#REJECTS[@]} - failed))" "${#REJECTS[@]}"
[[ $failed -eq 0 ]]
