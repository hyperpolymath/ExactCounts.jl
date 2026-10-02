# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# The database boundary, in its own project because the DuckDB Julia package is too
# large to make every `Pkg.test()` download. Run it with:
#
#     julia --project=test/boundaries -e 'using Pkg; Pkg.develop(path="."); Pkg.instantiate()'
#     julia --project=test/boundaries test/boundaries/runtests.jl

using ExactCounts
using Test, DuckDB

const NP = ExactCounts.NumericPolicy
const FIRST_UNREPRESENTABLE = big(2)^53 + 1          # 9007199254740993

@testset "the database boundary: DuckDB carries counts exactly, doubles do not" begin
    DBInterface = DuckDB.DBInterface
    con = DBInterface.connect(DuckDB.DB)
    row = collect(DBInterface.execute(con,
        "SELECT 9007199254740993::BIGINT AS exact, 9007199254740993::DOUBLE AS approx"))[1]

    # Exact: an integer column is a count, and it survives the round trip.
    @test row.exact == FIRST_UNREPRESENTABLE
    @test typeof(row.exact) === Int64

    # The negative control: the same literal in a DOUBLE column comes back as a
    # different integer, and nothing in the result marks it as wrong.
    @test row.approx != FIRST_UNREPRESENTABLE
    @test BigInt(row.approx) == big(2)^53

    # The ceiling is real and typed: past BIGINT a BIGINT column refuses rather than
    # rounding, which is the behaviour worth having.
    @test_throws DuckDB.QueryException collect(DBInterface.execute(con,
        "SELECT 18446744073709551616::BIGINT"))               # 2^64

    # DuckDB's own ceiling is 128-bit, and HUGEINT carries that exactly -- so the
    # database is not the limiting partner until 2^127.
    huge = collect(DBInterface.execute(con,
        "SELECT 170141183460469231731687303715884105727::HUGEINT"))[1][1]
    @test Int128(huge) == typemax(Int128)

    # Past everything the column type can hold, the string form transports the count
    # unchanged -- the same encoding the JSON and CSV boundaries use.
    beyond = big(2)^200 + 1
    stored = NP.to_storage(NP.exact_value(beyond))
    @test stored isa String
    cell = collect(DBInterface.execute(con, "SELECT '$stored'::VARCHAR"))[1][1]
    @test NP.parse_exact_count(cell) == beyond
end
