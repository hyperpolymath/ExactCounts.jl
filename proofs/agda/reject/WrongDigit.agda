-- SPDX-License-Identifier: MPL-2.0
-- MUST FAIL: 2/3 at two decimals is 0.67, not 0.66; the half-up spec must reject a wrong digit.
-- EXPECT: Data.Unit.⊤ !=<

module reject.WrongDigit where

open import Data.Integer using (+_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)
open import ExactCounts.DecimalRounding

wrong : IsRoundHalfUp (+ 2) 2 2 (+ 66)
wrong = toWitness {a? = isRoundHalfUp? (+ 2) 2 2 (+ 66)} tt
