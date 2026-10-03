<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->

# Bounded method catalogue, v1: the part this package implements

This is an **excerpt** of the bounded method catalogue for the MetaManifold
statistics layer, `docs/statistics/method-catalogue-v1.md` in
`hyperpolymath/MetaManifold-WebUI` at commit `c7e5a39`. The repository owner
(`@hyperpolymath`) approved that catalogue without amendment on 2026-09-22. The
excerpt below quotes the parts that govern ExactCounts.jl unchanged; the
original stays the record of the approval.

ExactCounts.jl implements **item 1 only**. Items 2 and 3 are planned as separate
packages and are not part of this package.

## v1 scope, item 1 (approved)

> 1. **Descriptive summaries at exact precision** — counts and proportions as exact
>    integers/rationals. No inference claimed. Depends only on `numeric_policy.jl`,
>    which this PR adds.

In this package, `numeric_policy.jl` is `ExactCounts.NumericPolicy` and the
summaries are `ExactCounts.ExactSummaries`. The published conditions for this
method are in
[`method-conditions/exact-descriptive-summaries.md`](method-conditions/exact-descriptive-summaries.md).

## Supported / unsupported conditions to be agreed with each method

> Every method above will publish, before implementation:
>
> - **Response type** it accepts (counts, proportions, distances, continuous) and what
>   it does with zeros, and with all-zero samples.
> - **Study design** it supports: pairing, blocking, repeated measures, covariates,
>   unequal sequencing depth, compositionality. Missing design information means a
>   descriptive summary, never a guess.
> - **Overdispersion and depth** handling, named explicitly, not absorbed into a
>   default.
> - **Uncertainty**: interval method, effect size, multiple-testing policy (BH is
>   mandatory where several tests are reported — an existing project rule).
> - **Diagnostics and warnings** surfaced to the user, in accessible language, including
>   the assumption that is most likely to be wrong for the data at hand.
> - **Computational limits**: time and memory bounds, and what happens at them
>   (`ResourceLimitError`, an explicit unsuccessful state).

## Explicitly not claimed (quoted as it bears on item 1)

> - Higher precision is not exactness (see `numeric-contracts.md`).

## What approval was given (2026-09-22)

> 1. ✅ The v1 scope above (items 1–3; item 4 stays deferred to #3).
> 2. ✅ The per-method publication list as the acceptance gate for each method.
> 3. ✅ The reading that a descriptive summary is the correct default whenever the
>    information needed for valid inference is missing.

The issue numbers (#1, #3) refer to `hyperpolymath/MetaManifold-WebUI`.
