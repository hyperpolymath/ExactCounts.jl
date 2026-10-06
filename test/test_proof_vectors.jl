# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# The bridge from the Agda proofs to the shipped Julia code.
#
# proofs/vectors/vectors.toml is extracted from proofs/agda/ExactCounts/Vectors.agda,
# whose every entry Agda has verified by computation.  Each one is reproduced here
# against the function it describes.  Every vector is also mutated by one unit and
# the mutant must be rejected, so a check that accepts anything cannot pass.
using ExactCounts
using Test, TOML

const NPV = ExactCounts.NumericPolicy

# The native signed type with `bits` bits, the machine side of Agda's `Fits (bits-1)`.
const SIGNED = Dict(8 => Int8, 16 => Int16, 32 => Int32, 64 => Int64)

"""Parse one integer field of a vector, which the TOML stores as a decimal string."""
vint(v, key) = parse(BigInt, v[key])

"""
    expected_decimal(m, s) -> String

The text a correct renderer prints for the scaled integer `m` at `s` decimal
places: the sign only when `m` is non-zero, then the magnitude's digits.
"""
function expected_decimal(m::Integer, s::Integer)
    sign_str = m < 0 ? "-" : ""
    a = abs(m)
    s == 0 && return string(sign_str, a)
    return string(sign_str, div(a, big(10)^s), ".", lpad(string(rem(a, big(10)^s)), s, "0"))
end

"""
    is_control(v) -> Bool

Whether `v` states a rule the shipped display does NOT implement: halves down
(`round_half_down`), or halves towards +∞ on a negative value (`round_half_up`
with a negative numerator).  Julia must disagree with every control.
"""
is_control(v) = v["kind"] == "round_half_down" ||
                (v["kind"] == "round_half_up" && vint(v, "numerator") < 0)

"""
    vector_holds(v) -> Bool

Whether the Julia implementation reproduces the known answer stated by vector `v`.
For a control vector (see `is_control`) it returns whether Julia AGREES with the
rule the control states, which must be false.
"""
function vector_holds(v)
    kind = v["kind"]
    if kind in ("round_half_away", "round_half_up", "round_half_down")
        n, d, s, m = vint(v, "numerator"), vint(v, "denominator"), Int(vint(v, "digits")), vint(v, "scaled")
        scaled = NPV._rounded_scaled(n, d, big(10)^s)
        rendered = NPV._rendered_decimal(n // d, s)
        return scaled == m && rendered == expected_decimal(m, s)
    elseif kind == "abundance"
        got = NPV.exact_relative_abundance(vint(v, "count"), vint(v, "total"))
        return got !== nothing && got == vint(v, "numerator") // vint(v, "denominator")
    elseif kind == "abundance_refused"
        c, t = vint(v, "count"), vint(v, "total")
        if v["refusal"] == "zeroTotal"
            return c <= t && NPV.exact_relative_abundance(c, t) === nothing
        else  # countExceedsTotal: refused as an argument error, before the zero-total test
            try
                NPV.exact_relative_abundance(c, t)
                return false
            catch err
                return err isa ArgumentError && occursin("exceeds", sprint(showerror, err))
            end
        end
    elseif kind == "fits"
        T = SIGNED[Int(vint(v, "bits"))]
        fits = try
            T(vint(v, "value")); true
        catch err
            err isa InexactError || rethrow(); false
        end
        return fits == v["fits"]
    elseif kind == "checked_sum"
        T = SIGNED[Int(vint(v, "bits"))]
        terms = T[T(parse(BigInt, x)) for x in v["terms"]]
        if haskey(v, "sum")
            got = try
                NPV.checked_count_sum(terms)
            catch err
                err isa NPV.CountOverflowError || rethrow(); nothing
            end
            return got isa T && got == vint(v, "sum")
        end
        try
            NPV.checked_count_sum(terms)
            return false
        catch err
            return err isa NPV.CountOverflowError
        end
    end
    error("unknown vector kind $(kind) in $(v["name"])")
end

"""
    mutant(v) -> Dict

`v` with its stated answer changed by one unit, or its verdict flipped, so a
correct implementation must reject it.
"""
function mutant(v)
    w = copy(v)
    kind = v["kind"]
    if kind in ("round_half_away", "round_half_up", "round_half_down")
        w["scaled"] = string(vint(v, "scaled") + 1)
    elseif kind == "abundance"
        w["numerator"] = string(vint(v, "numerator") + 1)
    elseif kind == "abundance_refused"
        w["refusal"] = v["refusal"] == "zeroTotal" ? "countExceedsTotal" : "zeroTotal"
    elseif kind == "fits"
        w["fits"] = !v["fits"]
    elseif kind == "checked_sum"
        if haskey(v, "sum")
            w["sum"] = string(vint(v, "sum") - 1)
        else
            delete!(w, "refusal"); w["sum"] = "0"
        end
    end
    return w
end

@testset "Agda known-answer vectors" begin
    path = joinpath(pkgdir(ExactCounts), "proofs", "vectors", "vectors.toml")
    doc = TOML.parsefile(path)
    vectors = doc["vector"]
    @test length(vectors) == doc["count"]
    @test length(vectors) > 0

    @testset "$(v["name"])" for v in vectors
        if is_control(v)
            # Positive control: these state a DIFFERENT tie rule, and Julia must not
            # satisfy them.  If it did, this test could not tell the rules apart.
            @test !vector_holds(v)
        else
            @test vector_holds(v)
            @test !vector_holds(mutant(v))
        end
    end

    @testset "the tie rule the proofs bind is the one display uses" begin
        ties = filter(v -> v["kind"] == "round_half_down", vectors)
        @test !isempty(ties)                            # the control is present
        @test all(v -> NPV._rounded_scaled(vint(v, "numerator"), vint(v, "denominator"),
                                           big(10)^Int(vint(v, "digits"))) == vint(v, "scaled") + 1, ties)
    end

    @testset "negative ties go away from zero, not towards +∞" begin
        negs = filter(v -> v["kind"] == "round_half_up" && vint(v, "numerator") < 0, vectors)
        aways = filter(v -> v["kind"] == "round_half_away" && vint(v, "numerator") < 0, vectors)
        @test !isempty(negs)                            # the control is present
        @test !isempty(aways)                           # and so is the sign case it controls
        @test all(v -> NPV._rounded_scaled(vint(v, "numerator"), vint(v, "denominator"),
                                           big(10)^Int(vint(v, "digits"))) == vint(v, "scaled") - 1, negs)
    end

    # Residue R-EC-2: Agda's `Fits k` is a (k+1)-bit two's-complement range.  The
    # vectors must pin that range at every native signed width at both ends, and the
    # overflow guard must trip exactly past typemax and typemin.
    @testset "R-EC-2: the model's width is the machine's width" begin
        fits = filter(v -> v["kind"] == "fits", vectors)
        for (bits, T) in SIGNED
            here = filter(v -> vint(v, "bits") == bits, fits)
            values = Set(vint(v, "value") for v in here)
            @test values == Set(big.([typemax(T), typemax(T) + big(1), typemin(T), typemin(T) - big(1)]))
            @test big(typemax(T)) + 1 == big(2)^(8 * sizeof(T) - 1)
            @test NPV.checked_count_sum(T[typemax(T) - one(T), one(T)]) == typemax(T)
            @test_throws NPV.CountOverflowError NPV.checked_count_sum(T[typemax(T), one(T)])
            @test_throws NPV.CountOverflowError NPV.checked_count_sum(T[typemin(T), -one(T)])
        end
    end
end

"""
    sweep_disagreements(rounds, rows) -> Int

How many sweep rows `[n, D, s, m]` the rule `rounds(n, D, s, m)` contradicts.
A count, never a parity, so any number of failures is visible.
"""
sweep_disagreements(rounds, rows) = count(r -> !rounds(big.(r)...), rows)

"""
    julia_rounds(n, D, s, m) -> Bool

Whether the shipped display rounds `n/D` to the scaled integer `m` at `s`
places, and renders it as the matching decimal text.
"""
julia_rounds(n, D, s, m) =
    NPV._rounded_scaled(n, D, big(10)^Int(s)) == m &&
    NPV._rendered_decimal(n // D, Int(s)) == expected_decimal(m, Int(s))

@testset "Agda-certified rounding sweep" begin
    path = joinpath(pkgdir(ExactCounts), "proofs", "vectors", "sweep.toml")
    doc = TOML.parsefile(path)
    rows = doc["rows"]
    @test length(rows) == doc["count"]
    @test length(rows) > 0

    # Every row Agda certified, reproduced by Julia.
    @test sweep_disagreements(julia_rounds, rows) == 0

    # Controls: the sweep tells the shipped rule apart from its neighbours.
    ties_to_even(n, D, s, m) = round(BigInt, n * big(10)^Int(s) // D, RoundNearest) == m
    ties_up(n, D, s, m) = fld(2 * n * big(10)^Int(s) + D, 2 * D) == m
    @test sweep_disagreements(ties_to_even, rows) > 0
    @test sweep_disagreements(ties_up, rows) > 0

    # One wrong row is seen as exactly one failure.
    planted = copy(rows)
    k = findfirst(r -> r[1] < 0 && r[2] == 8 && r[3] == 2, planted)
    planted[k] = [planted[k][1], planted[k][2], planted[k][3], planted[k][4] + 1]
    @test sweep_disagreements(julia_rounds, planted) == 1
end
