<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# ExactCounts.jl

Exact counts and proportions for count tables, with every rounding marked as a
rounding.

- **Counts** stay integers of unbounded width. A float is accepted as a count only if
  it is finite, integral and within 2^53. Beyond that a `Float64` cannot say which
  integer it holds, so it is refused.
- **Sums** never wrap. `checked_count_sum` refuses on overflow (or widens to
  `BigInt` if asked).
- **Proportions** are `Rational{BigInt}`, so the proportions of a sample sum to
  exactly 1. A sample with zero reads returns `nothing`, because it has no
  composition, not a composition of zeros.
- **Display** is the only place rounding happens. The text says it is a rendering,
  and exact halves round away from zero.
- **Storage/JSON** keeps exact values exact: integers beyond 2^53 and rationals are
  written as strings.

The package describes and does not test. It produces no p-values, intervals or
comparisons. See
[`docs/method-conditions/exact-descriptive-summaries.md`](docs/method-conditions/exact-descriptive-summaries.md)
for what is claimed and what is not, and [`docs/numeric-contracts.md`](docs/numeric-contracts.md)
for the conversion rules.

```julia
julia> using ExactCounts

julia> s = exact_summary([1 2; 0 1]; sample_labels = ["a", "b"], feature_labels = ["f1", "f2"]);

julia> s.samples[2].proportions
2-element Vector{Union{Nothing, Rational{BigInt}}}:
 2//3
 1//3

julia> print(summary_to_display(s; digits = 2))
Descriptive summary — counts and proportions are exact. No comparison, no test and no significance is claimed.
  sample a — total 1
    f1: 1/1 (exact; 2dp = 1.00)
    f2: 0/1 (exact; 2dp = 0.00)
  sample b — total 3
    f1: 2/3 (exact; 2dp = 0.67)
    f2: 1/3 (exact; 2dp = 0.33)
```

The matrix has one row per feature and one column per sample.

## Install

The package is not in the General registry. You can install it in either of two ways:

```julia
# 1. by URL and tag, with no registry (Julia 1.11+ `[sources]`, or directly):
using Pkg; Pkg.add(url = "https://github.com/hyperpolymath/ExactCounts.jl", rev = "v0.1.0")

# 2. through the hyperpolymath registry:
using Pkg
Pkg.Registry.add(url = "https://github.com/hyperpolymath/julia-professional-registry")
Pkg.add("ExactCounts")
```

## Tests

```sh
julia --project -e 'using Pkg; Pkg.test()'
```

The suite includes independent cross-checks. Where the partner tool is absent, the
check is skipped and the skip is reported by name:

- a BigInt fraction reference run under [bun](https://bun.sh);
- the R and JavaScript boundaries, which show that doubles lose counts above 2^53;
- an opt-in DuckDB boundary: `julia --project=test/boundaries test/boundaries/runtests.jl`.

## Proofs

`proofs/` holds Agda proofs (`--safe --without-K`) of three properties:

- the overflow guard is exact;
- a sample's proportions sum to exactly 1, and its refusals come in the documented order;
- the decimal rendering satisfies its rounding specification.

Known-answer vectors extracted from the checked proofs are reproduced by the Julia
tests. [`proofs/PROOF-STATUS.md`](proofs/PROOF-STATUS.md) maps each theorem to the
function and the test that bind it, and lists what is not proved.

## Licence

Code is MPL-2.0 and prose is CC-BY-SA-4.0, declared per file by SPDX header.
MPL-2.0 is compatible with GPL-family licences, including AGPL-3.0, under MPL-2.0 §3.3
(Secondary Licenses), so AGPL-3.0 projects can depend on this package without
relicensing.
