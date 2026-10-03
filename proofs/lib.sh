# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Shared toolchain resolution for the proof scripts.  Sourced, not executed.
#
# The proofs are checked against one pinned toolchain: Agda 2.6.4.3 and
# agda-stdlib 2.1, which are exactly Debian 13 (trixie)'s `agda` and
# `agda-stdlib` packages (residue R-TC-1).  Any other Agda is refused rather than
# tried, because "it type-checked on something" is not the claim being made.
#
#   AGDA_BIN         path to an agda binary (default: /usr/bin/agda, then PATH)
#   AGDA_STDLIB_LIB  path to standard-library.agda-lib
#                    (default: /usr/share/agda-stdlib/standard-library.agda-lib)

PROOFS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
AGDA_DIR="$PROOFS_DIR/agda"
AGDA_PINNED_VERSION="2.6.4.3"
STDLIB_PINNED_NAME="standard-library-2.1"

# Print an error naming the calling script and exit non-zero.
die() { printf '%s: FATAL: %s\n' "$(basename "$0")" "$*" >&2; exit 1; }

# Set AGDA to the pinned Agda binary, or die naming what was found instead.
resolve_agda() {
  local cand found=""
  for cand in "${AGDA_BIN:-}" /usr/bin/agda "$(command -v agda 2>/dev/null || true)"; do
    [[ -n "$cand" && -x "$cand" ]] || continue
    if [[ "$("$cand" --version 2>/dev/null)" == "Agda version $AGDA_PINNED_VERSION" ]]; then
      AGDA="$cand"
      return 0
    fi
    found+=" $cand=($("$cand" --version 2>/dev/null))"
  done
  die "Agda $AGDA_PINNED_VERSION not found (apt install agda, or set AGDA_BIN); saw:${found:- nothing}"
}

# Set STDLIB_LIB to the pinned standard library's .agda-lib file, or die.
resolve_stdlib() {
  STDLIB_LIB="${AGDA_STDLIB_LIB:-/usr/share/agda-stdlib/standard-library.agda-lib}"
  [[ -f "$STDLIB_LIB" ]] || die "standard library not found at $STDLIB_LIB (apt install agda-stdlib, or set AGDA_STDLIB_LIB)"
  grep -qx "name: $STDLIB_PINNED_NAME" "$STDLIB_LIB" \
    || die "$STDLIB_LIB is not $STDLIB_PINNED_NAME: $(grep -m1 '^name:' "$STDLIB_LIB")"
}

# Write an Agda libraries file for the proof tree rooted at $2 into path $1.
write_libraries() {
  printf '%s\n%s\n' "$2/exactcounts-proofs.agda-lib" "$STDLIB_LIB" > "$1"
}
