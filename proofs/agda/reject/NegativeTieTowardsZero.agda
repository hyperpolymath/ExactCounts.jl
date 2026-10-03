-- SPDX-License-Identifier: MPL-2.0
-- MUST FAIL: the shipped rule takes a negative half away from zero; claiming −1/2 at 0 dp is 0 must be rejected, or the sign case of IsRoundHalfAway is vacuous.
-- EXPECT: Data.Unit.⊤ !=<

module reject.NegativeTieTowardsZero where

open import Data.Integer using (+_; -[1+_])
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)
open import ExactCounts.DecimalRounding

wrong : IsRoundHalfAway -[1+ 0 ] 1 0 (+ 0)
wrong = toWitness {a? = isRoundHalfAway? -[1+ 0 ] 1 0 (+ 0)} tt
