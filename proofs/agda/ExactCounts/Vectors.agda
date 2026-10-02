-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Known-answer vectors: the bridge from the proofs to the Julia code.
--
-- Every `vec-*` definition below is a concrete fact the type-checker has
-- verified by computation, and `proofs/extract-vectors.js` turns each one into a
-- JSON record that `test/proof_vectors.jl` reproduces against the shipped Julia
-- functions.  So a vector is not a number typed into two places: if a value here
-- were wrong this module would not type-check, and if the Julia code disagreed
-- with it the Julia test would fail.
--
-- The extractor reads only declarations named `vec-*`, and only in the shapes
-- written here.  A `vec-*` signature it cannot parse is an extraction error, not
-- a silent omission.  Keep each signature on one line.
--
-- Rounding vectors re-export the lemmas in `DecimalRounding` by name, so the
-- vector and the lemma are one fact: the alias type-checks only if the types
-- are identical.

{-# OPTIONS --without-K --safe #-}

module ExactCounts.Vectors where

open import ExactCounts.Prelude
open import ExactCounts.Counts
open import ExactCounts.Proportions
open import ExactCounts.DecimalRounding

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Rational.Unnormalised using (mkℚᵘ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True; False; toWitness)

------------------------------------------------------------------------
-- Decimal rounding
--
-- `IsRoundHalfUp` is the rule `to_display` implements on non-negative values.
-- The `IsRounding` tie vectors are the positive control: Julia must DISAGREE
-- with them, which shows the Julia check can tell the two rules apart.

vec-half-up-2/3-at-2dp : IsRoundHalfUp (+ 2) 2 2 (+ 67)
vec-half-up-2/3-at-2dp = agreement-2/3

vec-half-up-1/3-at-2dp : IsRoundHalfUp (+ 1) 2 2 (+ 33)
vec-half-up-1/3-at-2dp = agreement-1/3

vec-half-up-5/8-at-3dp : IsRoundHalfUp (+ 5) 7 3 (+ 625)
vec-half-up-5/8-at-3dp = agreement-5/8

vec-half-up-one-at-2dp : IsRoundHalfUp (+ 1) 0 2 (+ 100)
vec-half-up-one-at-2dp = agreement-one

vec-half-up-1/2-at-0dp : IsRoundHalfUp (+ 1) 1 0 (+ 1)
vec-half-up-1/2-at-0dp = half-ties-round-up

vec-half-up-1/8-at-2dp : IsRoundHalfUp (+ 1) 7 2 (+ 13)
vec-half-up-1/8-at-2dp = toWitness {a? = isRoundHalfUp? (+ 1) 7 2 (+ 13)} _

vec-half-up-zero-at-2dp : IsRoundHalfUp (+ 0) 0 2 (+ 0)
vec-half-up-zero-at-2dp = toWitness {a? = isRoundHalfUp? (+ 0) 0 2 (+ 0)} _

vec-half-down-1/2-at-0dp : IsRounding (+ 1) 1 0 (+ 0)
vec-half-down-1/2-at-0dp = half-ties-round-down

vec-half-down-1/8-at-2dp : IsRounding (+ 1) 7 2 (+ 12)
vec-half-down-1/8-at-2dp = toWitness {a? = isRounding? (+ 1) 7 2 (+ 12)} _

------------------------------------------------------------------------
-- Relative abundance, including the order the refusals are checked in

vec-abundance-2-of-3 : relativeAbundance 2 3 ≡ value (mkℚᵘ (+ 2) 2)
vec-abundance-2-of-3 = refl

vec-abundance-3-of-3 : relativeAbundance 3 3 ≡ value (mkℚᵘ (+ 3) 2)
vec-abundance-3-of-3 = refl

vec-abundance-0-of-5 : relativeAbundance 0 5 ≡ value (mkℚᵘ (+ 0) 4)
vec-abundance-0-of-5 = refl

vec-abundance-0-of-0 : relativeAbundance 0 0 ≡ refused zeroTotal
vec-abundance-0-of-0 = refl

-- count ≤ total is checked first, so 1 of 0 is "exceeds", not "zero total".
vec-abundance-1-of-0 : relativeAbundance 1 0 ≡ refused countExceedsTotal
vec-abundance-1-of-0 = refl

vec-abundance-4-of-3 : relativeAbundance 4 3 ≡ refused countExceedsTotal
vec-abundance-4-of-3 = refl

------------------------------------------------------------------------
-- The fixed-width bound, at every native signed width
--
-- `Fits k` is the range of a (k+1)-bit two's-complement integer.  The Julia
-- side checks each vector against `typemin`/`typemax` of Int8 … Int64, which
-- is what ties the model's `k` to the machine (residue R-EC-2).

vec-fits-7-max : True (fits? 7 (+ 127))
vec-fits-7-max = _

vec-fits-7-over : False (fits? 7 (+ 128))
vec-fits-7-over = _

vec-fits-7-min : True (fits? 7 (-[1+ 127 ]))
vec-fits-7-min = _

vec-fits-7-under : False (fits? 7 (-[1+ 128 ]))
vec-fits-7-under = _

vec-fits-15-max : True (fits? 15 (+ 32767))
vec-fits-15-max = _

vec-fits-15-over : False (fits? 15 (+ 32768))
vec-fits-15-over = _

vec-fits-15-min : True (fits? 15 (-[1+ 32767 ]))
vec-fits-15-min = _

vec-fits-15-under : False (fits? 15 (-[1+ 32768 ]))
vec-fits-15-under = _

vec-fits-31-max : True (fits? 31 (+ 2147483647))
vec-fits-31-max = _

vec-fits-31-over : False (fits? 31 (+ 2147483648))
vec-fits-31-over = _

vec-fits-31-min : True (fits? 31 (-[1+ 2147483647 ]))
vec-fits-31-min = _

vec-fits-31-under : False (fits? 31 (-[1+ 2147483648 ]))
vec-fits-31-under = _

vec-fits-63-max : True (fits? 63 (+ 9223372036854775807))
vec-fits-63-max = _

vec-fits-63-over : False (fits? 63 (+ 9223372036854775808))
vec-fits-63-over = _

vec-fits-63-min : True (fits? 63 (-[1+ 9223372036854775807 ]))
vec-fits-63-min = _

vec-fits-63-under : False (fits? 63 (-[1+ 9223372036854775808 ]))
vec-fits-63-under = _

------------------------------------------------------------------------
-- Checked sums: the operation `checked_count_sum` implements

-- A bounded value, built only when the decision procedure says it fits.
bnd : (k : ℕ) (v : ℤ) {f : True (fits? k v)} → Bounded k
bnd k v {f} = mkBounded v (toWitness f)

-- The value a checked operation returned, with the range proof forgotten, so
-- a vector can state the number without stating a proof term.
result : ∀ {k} → Checked (Bounded k) → Checked ℤ
result (ok b)      = ok (intValue b)
result (refused r) = refused r

vec-sum-63-reaches-max : result (checkedSumOf (bnd 63 (+ 9223372036854775806)) (bnd 63 (+ 1) ∷ [])) ≡ ok (+ 9223372036854775807)
vec-sum-63-reaches-max = refl

vec-sum-63-overflows : result (checkedSumOf (bnd 63 (+ 9223372036854775807)) (bnd 63 (+ 1) ∷ [])) ≡ refused overflow
vec-sum-63-overflows = refl

vec-sum-63-underflows : result (checkedSumOf (bnd 63 (-[1+ 9223372036854775807 ])) (bnd 63 (-[1+ 0 ]) ∷ [])) ≡ refused overflow
vec-sum-63-underflows = refl

vec-sum-63-three-terms : result (checkedSumOf (bnd 63 (+ 4611686018427387904)) (bnd 63 (+ 4611686018427387903) ∷ bnd 63 (+ 1) ∷ [])) ≡ refused overflow
vec-sum-63-three-terms = refl

vec-sum-7-overflows : result (checkedSumOf (bnd 7 (+ 100)) (bnd 7 (+ 28) ∷ [])) ≡ refused overflow
vec-sum-7-overflows = refl

vec-sum-7-fits : result (checkedSumOf (bnd 7 (+ 100)) (bnd 7 (+ 27) ∷ [])) ≡ ok (+ 127)
vec-sum-7-fits = refl
