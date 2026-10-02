-- SPDX-License-Identifier: MPL-2.0
-- MUST FAIL: count <= total is checked before the zero-total test, so 1 of 0 is countExceedsTotal; the docstring-reading answer must be rejected.
-- EXPECT: countExceedsTotal != zeroTotal

module reject.RefusalOrder where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ExactCounts.Prelude using (refused; zeroTotal)
open import ExactCounts.Proportions using (relativeAbundance)

wrong : relativeAbundance 1 0 ≡ refused zeroTotal
wrong = refl
