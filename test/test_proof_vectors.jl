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
    vector_holds(v) -> Bool

Whether the Julia implementation reproduces the known answer stated by vector `v`.
For a `round_half_down` vector it returns whether Julia AGREES with that rule.
"""
function vector_holds(v)
    kind = v["kind"]
    if kind in ("round_half_up", "round_half_down")
        n, d, s, m = vint(v, "numerator"), vint(v, "denominator"), Int(vint(v, "digits")), vint(v, "scaled")
        scaled = NPV._rounded_scaled(n, d, big(10)^s)
        rendered = NPV._rendered_decimal(n // d, s)
        expected = s == 0 ? string(m) : string(div(m, big(10)^s), ".", lpad(string(rem(m, big(10)^s)), s, "0"))
        return scaled == m && rendered == expected
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
    if kind in ("round_half_up", "round_half_down")
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
        if v["kind"] == "round_half_down"
            # Positive control: these state the OTHER tie rule, and Julia must not
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
