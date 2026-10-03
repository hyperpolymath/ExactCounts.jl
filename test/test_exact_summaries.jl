# SPDX-License-Identifier: MPL-2.0
# Evidence for catalogue item 1, held to the conditions published in
# docs/method-conditions/exact-descriptive-summaries.md before the
# implementation existed. Each testset below is one of the four things that document
# requires: known answers derived by hand, an independent reference, negative controls,
# and proof that nothing outside this module changed.

using Test
using ExactCounts

@testset "exact descriptive summaries" begin

    @testset "known answers, derived by hand" begin
        # features x samples: f1 = (4, 6), f2 = (0, 3)
        counts = [4 6;
                  0 3]
        summary = exact_summary(counts;
                                sample_labels = ["a", "b"],
                                feature_labels = ["f1", "f2"])

        @test summary.approximate == false
        @test [s.label for s in summary.samples] == ["a", "b"]

        # Worked by hand, not read off the output:
        #   a: total 4 -> f1 = 4/4 = 1, f2 = 0/4 = 0
        #   b: total 9 -> f1 = 6/9 = 2/3, f2 = 3/9 = 1/3
        a, b = summary.samples
        @test a.total == 4
        @test a.proportions == [big(1) // big(1), big(0) // big(1)]
        @test b.total == 9
        @test b.proportions == [big(2) // big(3), big(1) // big(3)]

        # A zero count in a sample that has reads is exactly zero -- a value, not a
        # missing one. The distinction from the zero-total case below is the point.
        @test !isnothing(a.proportions[2])
        @test a.proportions[2] == 0        # exactly zero, and provably a Rational
        @test has_defined_proportions(a)

        # The representation itself is the claim: a Float64 here would round, and the
        # rounding would be invisible downstream.
        @test all(p -> p isa Rational{BigInt}, b.proportions)

        # Thirds and fifths have no exact binary form, so the exact values cannot be
        # reproduced by the float that would normally carry them.
        thirds = exact_summary(reshape([1, 2, 2], 3, 1);
                               sample_labels = ["c"],
                               feature_labels = ["g1", "g2", "g3"]).samples[1]
        @test thirds.total == 5
        @test thirds.proportions == [big(1) // big(5), big(2) // big(5), big(2) // big(5)]
        @test sum(thirds.proportions) == big(1) // big(1)   # exact, not 0.9999...
        @test Float64(big(1) // big(3)) != big(1) // big(3)
    end

    @testset "counts past 2^53 survive exactly" begin
        # The probe is the smallest integer a Float64 cannot hold, from the boundary
        # audit (test_numeric_boundaries.jl). Here it is a count, and the summary is the reason the audit
        # mattered: this number cannot pass through a float, so it must not have to.
        huge = big(2)^53 + 1
        summary = exact_summary(reshape([huge, big(1)], 2, 1);
                                sample_labels = ["deep"],
                                feature_labels = ["f1", "f2"])
        deep = summary.samples[1]

        @test deep.total == huge + 1
        @test deep.proportions[1] == huge // (huge + 1)
        @test deep.proportions[2] == big(1) // (huge + 1)
        @test numerator(deep.proportions[1]) == huge

        # The float claim fails, which is the whole reason for the string boundary.
        @test Float64(huge) == big(2)^53

        # A total beyond Int64 is widened, not wrapped: a wrapped total is a wrong
        # number that no downstream check can detect.
        #
        # The inputs here are Int64 ON PURPOSE, and the trap is real: Julia's own sum
        # wraps on exactly this fixture, which the assertion below demonstrates rather
        # than asserts in prose. An implementation that adds these counts naively returns
        # a negative total, and the assertion above fails.
        #
        # What this test does NOT claim: that the widening flag in the module is what
        # saves it. Counts leave the boundary as BigInt, so the accumulator cannot
        # overflow either way -- removing the flag still passes, which mutation testing
        # showed. The claim under test is the total, not the mechanism; a mechanism test
        # here would be testing an implementation choice.
        @test sum([typemax(Int64), 1]) < 0            # the naive sum wraps: the trap is real
        @test sum([typemax(Int64), 1]) != big(2)^63
        overflow = exact_summary(reshape([typemax(Int64), 1], 2, 1);
                                 sample_labels = ["wide"], feature_labels = ["f1", "f2"])
        @test overflow.samples[1].total == big(2)^63
        @test overflow.samples[1].total > 0
        @test overflow.samples[1].proportions ==
              [(big(2)^63 - 1) // big(2)^63, big(1) // big(2)^63]
    end

    @testset "a zero-total sample has no proportions (negative control)" begin
        counts = [0 5;
                  0 0]
        summary = exact_summary(counts;
                                sample_labels = ["empty", "fine"],
                                feature_labels = ["f1", "f2"])
        empty, fine = summary.samples

        @test empty.total == 0
        @test has_defined_proportions(empty) == false
        @test all(isnothing, empty.proportions)

        # The control: not zero, not NaN, not a float. A proportion that does not exist
        # must not be representable as a number at all.
        @test !any(p -> p == 0, empty.proportions)
        @test !any(p -> p isa AbstractFloat, empty.proportions)

        # And it says which sample, in words, without anyone having to infer it.
        @test any(w -> occursin("empty", w) && occursin("zero", lowercase(w)), empty.warnings)

        # A sample with reads in the same table is unaffected: the undefined state is
        # per sample, not a property of the table.
        @test has_defined_proportions(fine)
        @test fine.proportions == [big(1) // big(1), big(0) // big(1)]

        # An all-zero table is a real observation, not an error.
        allzero = exact_summary(zeros(Int, 2, 1);
                                sample_labels = ["z"], feature_labels = ["f1", "f2"])
        @test allzero.samples[1].total == 0
        @test all(isnothing, allzero.samples[1].proportions)
    end

    @testset "per-group summaries aggregate exactly, and compare nothing" begin
        counts = [4 6 1;
                  0 3 2]
        summary = exact_summary(counts;
                                sample_labels = ["a", "b", "c"],
                                feature_labels = ["f1", "f2"],
                                groups = ["A", "B", "A"])

        @test length(summary.groups) == 2
        A = summary.groups[1]
        @test A.label == "A"
        @test A.members == ["a", "c"]          # exact members, named
        @test A.counts == [BigInt(5), BigInt(2)]   # 4+1 and 0+2, in integers
        @test A.total == 7
        @test A.proportions == [big(5) // big(7), big(2) // big(7)]

        # Aggregation is a sum of counts, not a mean of proportions: with depths 4 and 3
        # the two differ, and only one of them is the group's composition.
        mean_of_proportions = (big(1) // big(1) + big(1) // big(3)) / 2
        @test A.proportions[1] != mean_of_proportions

        # A group whose members have no reads at all is undefined, exactly like a
        # zero-total sample -- grouping must not quietly manufacture a composition.
        zero_group = exact_summary(counts;
                                   sample_labels = ["a", "b", "c"],
                                   feature_labels = ["f1", "f2"],
                                   groups = ["A", "B", "A"]).groups[1]
        @test has_defined_proportions(zero_group)

        empty_group = exact_summary([0 1; 0 2];
                                    sample_labels = ["x", "y"],
                                    feature_labels = ["f1", "f2"],
                                    groups = ["E", "F"]).groups[1]
        @test empty_group.total == 0
        @test !has_defined_proportions(empty_group)
        @test all(isnothing, empty_group.proportions)

        # The shape people misread as a test says, in words, that it is not one.
        text = summary_to_display(summary)
        @test occursin("No comparison", text)
        @test occursin("no significance is claimed", text)
    end

    @testset "input that is not a count is refused by name (negative control)" begin
        # A non-integral value is not a count, and the refusal names the cell.
        err = try
            exact_summary(reshape([1.5, 2.0], 2, 1);
                          sample_labels = ["s1"], feature_labels = ["f1", "f2"])
            nothing
        catch e
            e
        end
        @test err isa UnsupportedRepresentationError
        @test occursin("f1", sprint(showerror, err))
        @test occursin("s1", sprint(showerror, err))

        # A float beyond 2^53 cannot say which integer it holds -- even when it is a
        # value that exists (2^53 + 2 is representable). Its history cannot be
        # inspected, so it is refused rather than trusted.
        @test_throws UnsupportedRepresentationError exact_summary(
            reshape([2.0^53 + 2, 1.0], 2, 1);
            sample_labels = ["s1"], feature_labels = ["f1", "f2"])

        # Negative counts are not counts of a table; that is a broken input, not a
        # rounding question.
        @test_throws ArgumentError exact_summary([-1 2];
                                                 sample_labels = ["s1"],
                                                 feature_labels = ["f1"])

        # Float input inside the exact range is ACCEPTED, and labelled: the conditions
        # allow an approximation to travel, never to travel unmarked.
        approximate = exact_summary([4.0 6.0;
                                     0.0 3.0];
                                    sample_labels = ["a", "b"],
                                    feature_labels = ["f1", "f2"])
        @test approximate.approximate == true
        @test any(w -> occursin("approximation", w), approximate.samples[1].warnings)
        @test approximate.samples[2].proportions == [big(2) // big(3), big(1) // big(3)]
        @test occursin("approximations", summary_to_display(approximate))
    end

    @testset "the budget raises instead of rounding (negative control)" begin
        # A prime total whose denominator cannot fit a 32-bit budget: the summary must
        # fail loudly rather than fall back to floats, because a silent downgrade from
        # exact to approximate is the failure this whole layer exists to prevent.
        tight = numeric_policy(; mode = :exact_counts, max_denominator_bits = 32)
        huge_prime = big(2)^61 - 1
        @test_throws ResourceLimitError exact_summary(
            reshape([huge_prime, big(1)], 2, 1);
            sample_labels = ["s"], feature_labels = ["f1", "f2"], policy = tight)

        # The same table under the default budget is fine: the limit is a budget, not a
        # defect in the data.
        generous = exact_summary(reshape([huge_prime, big(1)], 2, 1);
                                 sample_labels = ["s"], feature_labels = ["f1", "f2"])
        @test generous.samples[1].proportions[1] == huge_prime // (huge_prime + 1)
    end

    @testset "an ordinary policy cannot produce an exact summary" begin
        # Asking for exactness under the ordinary policy must fail by name. The failure
        # this prevents is a caller receiving Float64s that look exactly like the exact
        # answer would have looked, until somebody checks.
        err = try
            exact_summary([4 6; 0 3];
                          sample_labels = ["a", "b"], feature_labels = ["f1", "f2"],
                          policy = numeric_policy(:ordinary))
            nothing
        catch e
            e
        end
        @test err isa UnsupportedRepresentationError
        @test occursin("exact_counts", sprint(showerror, err))

        # Higher precision is not exactness: it moves the rounding error rather than
        # abolishing it, so it cannot be accepted here either.
        @test_throws UnsupportedRepresentationError exact_summary(
            [4 6; 0 3]; sample_labels = ["a", "b"], feature_labels = ["f1", "f2"],
            policy = numeric_policy(; mode = :high_precision, precision_bits = 256))
    end

    @testset "display renders signs and ties by integer arithmetic" begin
        # The rendering exists because a rounded decimal must never be what gets stored,
        # but it is still text a person reads, so it has to be right at the edges. The
        # implementation does this in integers; these are the cases a floating-point
        # renderer gets wrong, which is why they are here rather than assumed.
        @testset "negative rationals keep their sign, and only one" begin
            text = to_display(exact_value(-2 // 3))
            @test occursin("-0.666667", text)
            @test !occursin("--", text)
        end
        @testset "a true tie rounds away from zero in both directions" begin
            # 1/8 = 0.125 exactly, so at two decimals the tie is real and visible.
            @test occursin("0.13", to_display(exact_value(1 // 8); digits = 2))
            @test occursin("-0.13", to_display(exact_value(-1 // 8); digits = 2))
        end
        @testset "a negative value that rounds to zero has no sign" begin
            # The digits state the rounded value; -1/1000 at two decimals is zero,
            # and "-0.00" would state a sign the rounded value does not have.
            @test ExactCounts.NumericPolicy._rendered_decimal(-1 // 1000, 2) == "0.00"
            @test ExactCounts.NumericPolicy._rendered_decimal(-1 // 3, 0) == "0"
            @test ExactCounts.NumericPolicy._rendered_decimal(-1 // 200, 2) == "-0.01"   # the tie still moves away
            @test ExactCounts.NumericPolicy._rendered_decimal(-1 // 2, 0) == "-1"
        end
        @testset "values beyond Float64 still render as digits" begin
            # Float64 overflows its exact-integer range around 2^53; this is far past it,
            # so a float-based renderer would lose the integer part or switch to e+00.
            huge = (big(2)^200 + 1) // big(3)
            text = to_display(exact_value(huge))
            @test occursin(".666667", text)
            @test !occursin("e+", text)
            @test !occursin("E+", text)
        end
    end

    @testset "storage round-trips through the boundary readers" begin
        summary = exact_summary([4 6; 0 3];
                                sample_labels = ["a", "b"], feature_labels = ["f1", "f2"])
        stored = summary_to_storage(summary)

        @test stored["claim"] isa String
        @test occursin("no comparison", stored["claim"])
        @test stored["mode"] == "exact_counts"
        @test length(stored["policy_fingerprint"]) == 64

        b = stored["samples"][2]
        @test b["total"] == 9
        # Proportions travel as strings, never as JSON numbers: a JSON number on the way
        # through a browser is a Float64 (see the boundary audit).
        @test b["proportions"] == ["2/3", "1/3"]
        @test b["proportions_defined"] == true

        # The round trip: what was written parses back to the identical rational, so the
        # stored form loses nothing.
        @test parse_exact_rational(b["proportions"][1]) == big(2) // big(3)
        @test parse_exact_rational(b["proportions"][2]) == big(1) // big(3)

        # Undefined travels as null, and says it is undefined rather than zero.
        empty = summary_to_storage(exact_summary([0 5; 0 0];
                                                 sample_labels = ["empty", "fine"],
                                                 feature_labels = ["f1", "f2"]))
        @test empty["samples"][1]["proportions"] == [nothing, nothing]
        @test empty["samples"][1]["proportions_defined"] == false

        # Display and storage are different things: the rendering is marked as one.
        text = summary_to_display(summary)
        @test occursin("2/3 (exact; 6dp = 0.666667)", text)   # exact fraction, rendering beside it
        @test !occursin("0.6666669999", text)               # the rendering is rounded, not 80 digits
        @test !occursin("2/3 (exact;", b["proportions"][1])   # never what gets stored
    end

    @testset "independent reference: bun BigInt fractions" begin
        # Compared value by value against an independent implementation of exact rational
        # arithmetic, in another language, in another process: JavaScript BigInt with
        # its own Euclid gcd. Agreement is then evidence about the arithmetic rather than
        # about this module's agreement with itself.
        bun = Sys.which("bun")
        if isnothing(bun)
            @testset "bun absent — the independent reference did NOT run" begin
                @test_skip false
            end
        else
            counts = [7 3;
                      5 11;
                      13 2]
            summary = exact_summary(counts;
                                    sample_labels = ["a", "b"],
                                    feature_labels = ["f1", "f2", "f3"])
            # One line per sample: "total;n/d,n/d,..." -- plain text, so reading it back
            # needs no JSON library on this side either.
            script = join([
                "const counts = [[7n, 3n], [5n, 11n], [13n, 2n]];",
                "const gcd = (a, b) => { while (b !== 0n) { [a, b] = [b, a % b]; } return a; };",
                "for (let j = 0; j < counts[0].length; j++) {",
                "  const col = counts.map(row => row[j]);",
                "  const total = col.reduce((s, c) => s + c, 0n);",
                "  const props = col.map(c => { const g = gcd(c, total); return `\${c / g}/\${total / g}`; });",
                "  console.log(`\${total};\${props.join(',')}`);",
                "}",
            ], "\n")
            dir = mktempdir()
            program = joinpath(dir, "reference.js")
            write(program, script)
            lines = split(strip(read(`$bun $program`, String)), '\n')
            @test length(lines) == length(summary.samples)

            for (sample, line) in zip(summary.samples, lines)
                total, props = split(line, ';')
                @test string(sample.total) == total
                mine = [string(numerator(p), "/", denominator(p)) for p in sample.proportions]
                @test mine == split(props, ',')
            end
            for sample in summary.samples
                @test sum(sample.proportions) == big(1) // big(1)
            end
        end
    end

    @testset "a summary does not change the ambient policy" begin
        # Running a summary does not touch the ambient policy: the ordinary default is
        # still the default afterwards, which is what keeps concurrent analyses from
        # sharing a setting. (That a host pipeline does not call this module unless
        # asked is the host's to test; MetaManifold's adapter carries that check.)
        before = numeric_policy()
        @test before.mode === :ordinary
        exact_summary([4 6; 0 3]; sample_labels = ["a", "b"], feature_labels = ["f1", "f2"])
        @test numeric_policy().mode === :ordinary
        @test policy_fingerprint(numeric_policy()) == policy_fingerprint(numeric_policy(:ordinary))
    end
end
