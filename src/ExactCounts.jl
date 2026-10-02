# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Exact integer counts and exact rational proportions, with a numeric policy that
# refuses to let an exact value, an approximation and a display rounding pass for
# one another. Two submodules, re-exported here:
#
#   NumericPolicy    what a count is, overflow refusal, exact rationals under a size
#                    budget, and storage/JSON forms that round-trip exactly.
#   ExactSummaries   per-sample and per-group totals and relative abundances as
#                    Rational{BigInt}, with a zero total carried as undefined.
module ExactCounts

include("numeric_policy.jl")
include("exact_summaries.jl")

using .NumericPolicy
using .ExactSummaries

for name in (names(NumericPolicy)..., names(ExactSummaries)...)
    name in (:NumericPolicy, :ExactSummaries) && continue
    @eval export $name
end

export NumericPolicy, ExactSummaries

end # module ExactCounts
