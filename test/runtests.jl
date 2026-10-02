# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
using Test

@testset "ExactCounts" begin
    include("test_numeric_policy.jl")
    include("test_exact_summaries.jl")
    include("test_numeric_boundaries.jl")
end
