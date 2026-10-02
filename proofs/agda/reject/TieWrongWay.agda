-- SPDX-License-Identifier: MPL-2.0
-- MUST FAIL: under IsRounding an exact half goes down; claiming 1/2 at 0 dp is 1 must be rejected, or the two tie rules are indistinguishable.
-- EXPECT: Data.Unit.⊤ !=<

module reject.TieWrongWay where

open import Data.Integer using (+_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)
open import ExactCounts.DecimalRounding

wrong : IsRounding (+ 1) 1 0 (+ 1)
wrong = toWitness {a? = isRounding? (+ 1) 1 0 (+ 1)} tt
