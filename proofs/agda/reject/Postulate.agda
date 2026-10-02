-- SPDX-License-Identifier: MPL-2.0
-- MUST FAIL: `--safe` (from exactcounts-proofs.agda-lib, deliberately not repeated here) forbids postulates. Guards against the library flags being dropped.
-- EXPECT: Cannot postulate every-sample-has-composition with safe flag

module reject.Postulate where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import ExactCounts.Prelude using (Outcome; value; refused; zeroTotal)
open import ExactCounts.Proportions using (relativeAbundance)

postulate every-sample-has-composition : ∀ c t → relativeAbundance c t ≡ value _
