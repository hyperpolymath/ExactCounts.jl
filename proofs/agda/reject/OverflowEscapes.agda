-- SPDX-License-Identifier: MPL-2.0
-- MUST FAIL: 2^63 does not fit in 64 bits; a sum reaching it must be refused, not returned.
-- EXPECT: Refusal.overflow !=

module reject.OverflowEscapes where

open import Data.Integer using (ℤ; +_)
open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ExactCounts.Counts using (Checked; ok; checkedSumOf)
open import ExactCounts.Vectors using (bnd; result)

wrong : result (checkedSumOf (bnd 63 (+ 9223372036854775807)) (bnd 63 (+ 1) ∷ [])) ≡ ok (+ 9223372036854775808)
wrong = refl
