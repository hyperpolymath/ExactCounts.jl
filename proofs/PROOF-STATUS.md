<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Proof status: ExactCounts.jl

This file maps each theorem to the Julia function it is about, and to the test
that ties the two together. A theorem about a model is not a theorem about
Julia, so every row says how close the binding is:

- **proved**: the property is a theorem about the Agda model.
- **bound by vector**: known-answer vectors are extracted from the type-checked
  Agda (`proofs/vectors/vectors.toml`). `test/test_proof_vectors.jl` checks that
  Julia reproduces each one, and that a mutated copy of each vector fails.
- **tested only**: there is a Julia test but no theorem.
- **not stated**: there is no theorem and the behaviour is listed in
  [`residue/exact-counts.residue`](residue/exact-counts.residue).

## Toolchain

Agda 2.6.4.3 with agda-stdlib 2.1, the Debian 13 (trixie) packages.
`proofs/lib.sh` refuses any other Agda rather than trying it (residue R-TC-1).
Every module is checked under `--safe --without-K` (set in
`exactcounts-proofs.agda-lib`).

`proofs/check.sh` is the whole gate; `.github/workflows/ci.yml` runs it on every
push and pull request in a Debian 13 container with exactly those packages. It
runs four checks:

1. an axiom audit (no `postulate`, no unsafe pragma, no hole);
2. `All.agda` must type-check without warnings;
3. every `reject/*.agda` must FAIL to type-check with the exact error its
   `-- EXPECT:` line names;
4. `vectors.toml` must be byte-identical to a fresh extraction.

`tests/gate-selftest.sh` plants defects to show the gate can fail.

## Counts (`ExactCounts/Counts.agda`) ↔ `NumericPolicy.checked_count_sum`

| Theorem | Says | Julia | Binding |
|---|---|---|---|
| `checkedAdd-is-exact` | an accepted sum is the integer sum | `checked_count_sum` (two terms) | proved; bound by vector (`checked_sum`, 6) |
| `checkedAdd-never-refuses-a-sum-that-fits` | no false refusals | same | proved; bound by vector |
| `checkedAdd-refuses-exactly-when-it-must` | a refusal happens iff the sum leaves `Fits k` | same; throws `CountOverflowError` | proved; bound by vector; `reject/OverflowEscapes.agda` |
| `checkedAdd-refusal-is-overflow` (+ `refused-injective`) | the refusal is literally `overflow` | `CountOverflowError`, not another error | proved (R-EC-1 closed 2026-10-02) |
| `checkedSumOf-is-exact` | a non-empty fold that accepts returns the sum of all terms | `checked_count_sum` (n terms) | proved; bound by vector |
| `Fits k` ↔ `Int8/16/32/64` | the model's width is the machine's | `typemin`/`typemax` | **bound by vector** (`fits`, 16), and the "R-EC-2" testset checks both ends of all four widths. The width itself is not provable in Agda (R-EC-2) |
| empty collection → `0` | | `checked_count_sum(Int[])` | **tested only** (`test_numeric_policy.jl`); R-EC-3 |
| `on_overflow = :widen` | | promotes to `BigInt` | **tested only**; out of scope, R-EC-3 |

## Proportions (`ExactCounts/Proportions.agda`) ↔ `NumericPolicy.exact_relative_abundance`

| Theorem | Says | Binding |
|---|---|---|
| `value-is-the-quotient` | an accepted proportion is exactly `count / total` | proved; bound by vector (`abundance`, 3) |
| `value-has-nonzero-denominator` | no accepted value divides by zero | proved |
| `zero-total-is-refused` | `0 of 0` is refused | proved; Julia returns `nothing`; bound by vector (`abundance_refused`) |
| `count-exceeds-total-is-refused` | `count > total` is refused | proved; Julia throws `ArgumentError` naming "exceeds"; bound by vector |
| `zero-total-with-count-is-refused-as-exceeding` | `1 of 0` is "exceeds", not "zero total": the order of the checks | proved; bound by vector; `reject/RefusalOrder.agda` |
| `proportions-sum-to-one`, `proportions-sum-to-one-list` | a sample's proportions sum to exactly 1 | proved; Julia: `exact_summary` known-answer tests (**tested**, not vector-bound) |
| `aggregate-then-divide` | the sum of proportions = (sum of counts) / total | proved; `exact_summary` group tests (**tested**) |
| negative count or total → `ArgumentError` | | **not stated**: the model takes ℕ inputs |
| denominator budget → `ResourceLimitError` | | **not stated**: Julia-only resource policy, R-EC-4 |

The refusal order as a contract is in
[`docs/numeric-contracts.md`](../docs/numeric-contracts.md). Steps 2 and 3
(and their order) are proved, step 1 cannot arise in the model, and step 4 is
tested only.

## Display rounding (`ExactCounts/DecimalRounding.agda`) ↔ `NumericPolicy._rounded_scaled` / `_rendered_decimal` (used by `to_display` for exact values)

| Item | Says | Binding |
|---|---|---|
| `IsRoundHalfUp n d s m` | the integer interval spec for half-up rounding at `s` digits | spec; decidable (`isRoundHalfUp?`) |
| `IsRoundHalfAway n d s m` | the shipped rule: half up for n ≥ 0, mirrored for n < 0 | spec; decidable (`isRoundHalfAway?`) |
| `away-agrees-on-nonneg`, `away-mirror` | the two clauses above, as equations | proved (`refl`) |
| `unique-halfUp`, `unique-halfAway` | at most one `m` satisfies the spec | **proved**, so a vector pins the one digit string Julia may print |
| existence (some `m` always satisfies it) | | **not stated**: R-DR-1; every vector exhibits its own witness |
| 10 `round_half_away` vectors, 5 of them negative | includes −1/2 → −1, −1/8 → −0.13, −1/1000 → 0.00 (no sign) | bound by vector: both `_rounded_scaled` and the rendered string |
| 8 `round_half_up` + 2 `round_half_down` vectors | the half-up spec on n ≥ 0, plus **controls** | the controls (half-down, and half-up on a negative numerator) must DISAGREE with Julia. The testset "negative ties go away from zero, not towards +∞" checks that they do |
| `reject/TieWrongWay`, `reject/WrongDigit`, `reject/NegativeTieTowardsZero` | the spec rejects a wrong tie, a wrong digit, and a negative tie towards zero | must-fail controls |
| approximate values: `Base.round`, ties to even | | **not stated**: by design, R-DR-2 |

## Prelude (`ExactCounts/Prelude.agda`)

These are helpers (`sumℤ`, `Outcome`, vector sums). They carry no claim about
Julia on their own.

## What is not claimed

- Nothing here is a statement about the Julia compiler, `BigInt`, or `Rational`.
  The binding is by known-answer vectors, which are only as strong as the vectors
  chosen. Each vector is mutated in the test to show it can fail.
- The JSON, R, browser and database boundaries (`test_numeric_boundaries.jl`,
  `test/boundaries/`) are tested only.
