-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- The integer rounding spec is rounding under the rationals' own order
-- (residue R-DR-3).
--
-- `IsRoundHalfAway` in ExactCounts.DecimalRounding is written with every
-- denominator cleared by hand, so that it needs nothing but ℤ.  That makes it
-- easy to decide and to compute with, but "this is rounding to s decimal places"
-- was then only a *reading* of its inequalities.  This module states the rule
-- the way a reader would write it — with the standard library's rationals, their
-- `_/_`, `_+_`, `_-_`, `_≤_` and `_<_`, and nothing cleared:
--
--   x ≥ 0 :   m/10^s − 1/(2·10^s)  ≤  x  <  m/10^s + 1/(2·10^s)
--   x < 0 :   m/10^s − 1/(2·10^s)  <  x  ≤  m/10^s + 1/(2·10^s)
--
-- and proves it equivalent to the integer spec, first over unnormalised
-- rationals (ℚᵘ, whose order is cross-multiplication) and then over the
-- normalised ℚ (via `toℚᵘ`, which preserves and reflects the order).  The
-- strict side of each window is where an exact half goes: away from zero.

{-# OPTIONS --without-K --safe #-}

module ExactCounts.DecimalRoundingAdequacy where

open import ExactCounts.DecimalRounding
  using (pow10; pow10≡; IsRoundHalfUp; IsRoundHalfAway;
         unique-halfAway; roundHalfAway; roundHalfAway-sound)

open import Data.Integer.Base as ℤ
  using (ℤ; +_; -[1+_]; +[1+_]; -_; _*_; _+_; _-_)
import Data.Integer.Properties as ℤₚ
open import Data.Integer.Tactic.RingSolver using (solve-∀)
open import Data.Nat.Base as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

import Data.Rational.Unnormalised.Base as ℚᵘ
import Data.Rational.Unnormalised.Properties as ℚᵘₚ
open ℚᵘ using (ℚᵘ; mkℚᵘ; ↥_; ↧_; _≃_)
import Data.Rational.Base as ℚ
import Data.Rational.Properties as ℚₚ
open ℚ using (ℚ; mkℚ)

------------------------------------------------------------------------
-- Equivalence plumbing

private
  -- Composes two equivalences.
  _⟫_ : ∀ {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
  f ⟫ g = mk⇔ (λ a → Equivalence.to g (Equivalence.to f a))
              (λ c → Equivalence.from f (Equivalence.from g c))
  infixr 5 _⟫_

  -- Equivalence is symmetric.
  flip⇔ : ∀ {A B : Set} → A ⇔ B → B ⇔ A
  flip⇔ f = mk⇔ (Equivalence.from f) (Equivalence.to f)

  -- Two equivalences give one on the pair.
  _×⇔_ : ∀ {A B C D : Set} → A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
  f ×⇔ g = mk⇔ (λ (a , c) → Equivalence.to f a , Equivalence.to g c)
               (λ (b , d) → Equivalence.from f b , Equivalence.from g d)

------------------------------------------------------------------------
-- The rational statement

-- The scale `10^s`, as the natural number a reader would write.
scale : ℕ → ℕ
scale s = 10 ℕ.^ s

-- `10^s` is never zero, so it may be a denominator.  Passed explicitly:
-- instance search on `10 ^ s` tries to invert `_^_` and gives up.
scale-nz : ∀ s → ℕ.NonZero (scale s)
scale-nz s = ℕₚ.m^n≢0 10 s

-- …and neither is `2·10^s`.
twice-nz : ∀ s → ℕ.NonZero (2 ℕ.* scale s)
twice-nz s = ℕₚ.m*n≢0 2 (scale s) {{_}} {{scale-nz s}}

-- The candidate digit string `m` read as the rational `m/10^s`.
digitᵘ : ℤ → ℕ → ℚᵘ
digitᵘ m s = ℚᵘ._/_ m (scale s) {{scale-nz s}}

-- Half a unit in the last place: `1/(2·10^s)`.
halfUlpᵘ : ℕ → ℚᵘ
halfUlpᵘ s = ℚᵘ._/_ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}

-- `m` is `x` rounded to `s` decimal places, exact halves away from zero,
-- stated with ℚᵘ's own arithmetic and order.  The sign of `x` is read with
-- ℚᵘ's order too, not from its representation.
RoundsHalfAwayᵘ : ℚᵘ → ℕ → ℤ → Set
RoundsHalfAwayᵘ x s m =
  (ℚᵘ.0ℚᵘ ℚᵘ.≤ x → (digitᵘ m s ℚᵘ.- halfUlpᵘ s ℚᵘ.≤ x)
                  × (x ℚᵘ.< digitᵘ m s ℚᵘ.+ halfUlpᵘ s))
  × (x ℚᵘ.< ℚᵘ.0ℚᵘ → (digitᵘ m s ℚᵘ.- halfUlpᵘ s ℚᵘ.< x)
                    × (x ℚᵘ.≤ digitᵘ m s ℚᵘ.+ halfUlpᵘ s))

-- The candidate digit string over the normalised rationals.
digitℚ : ℤ → ℕ → ℚ
digitℚ m s = ℚ._/_ m (scale s) {{scale-nz s}}

-- Half a unit in the last place over the normalised rationals.
halfUlpℚ : ℕ → ℚ
halfUlpℚ s = ℚ._/_ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}

-- The same rule over the normalised rationals, with ℚ's arithmetic and order.
RoundsHalfAwayℚ : ℚ → ℕ → ℤ → Set
RoundsHalfAwayℚ x s m =
  (ℚ.0ℚ ℚ.≤ x → (digitℚ m s ℚ.- halfUlpℚ s ℚ.≤ x)
               × (x ℚ.< digitℚ m s ℚ.+ halfUlpℚ s))
  × (x ℚ.< ℚ.0ℚ → (digitℚ m s ℚ.- halfUlpℚ s ℚ.< x)
                 × (x ℚ.≤ digitℚ m s ℚ.+ halfUlpℚ s))

------------------------------------------------------------------------
-- Numerators and denominators of the window's ends

private
  -- `n / P` has numerator `n`, whatever `P` is.
  ↥/ : ∀ n P .{{_ : ℕ.NonZero P}} → ↥ (n ℚᵘ./ P) ≡ n
  ↥/ n (suc _) = refl

  -- `n / P` has denominator `P`.
  ↧/ : ∀ n P .{{_ : ℕ.NonZero P}} → ↧ (n ℚᵘ./ P) ≡ + P
  ↧/ n (suc _) = refl

  -- The numerator of a sum is the cross-multiplied sum of numerators.
  ↥+ : ∀ p q → ↥ (p ℚᵘ.+ q) ≡ ↥ p * ↧ q + ↥ q * ↧ p
  ↥+ (mkℚᵘ _ _) (mkℚᵘ _ _) = refl

  -- The denominator of a sum is the product of the denominators.
  ↧+ : ∀ p q → ↧ (p ℚᵘ.+ q) ≡ ↧ p * ↧ q
  ↧+ (mkℚᵘ _ a) (mkℚᵘ _ b) = ℤₚ.pos-* (suc a) (suc b)

  -- Negation negates the numerator.
  ↥neg : ∀ p → ↥ (ℚᵘ.- p) ≡ - ↥ p
  ↥neg (mkℚᵘ _ _) = refl

  -- Negation keeps the denominator.
  ↧neg : ∀ p → ↧ (ℚᵘ.- p) ≡ ↧ p
  ↧neg (mkℚᵘ _ _) = refl

  -- `+ (2·P)` is `+ 2 * + P`.
  pos-2* : ∀ P → + (2 ℕ.* P) ≡ + 2 * + P
  pos-2* P = ℤₚ.pos-* 2 P

  lo-num-eq : ∀ m S → m * (+ 2 * S) + (- (+ 1)) * S ≡ m * (+ 2 * S) - S
  lo-num-eq = solve-∀

  -- `m/10^s − 1/(2·10^s)` has numerator `m·2S − S` (S = 10^s).
  ↥lo : ∀ m s → ↥ (digitᵘ m s ℚᵘ.- halfUlpᵘ s)
                  ≡ m * (+ 2 * + scale s) - + scale s
  ↥lo m s = trans (↥+ (digitᵘ m s) (ℚᵘ.- halfUlpᵘ s))
    (trans (cong₂ _+_
              (cong₂ _*_ (↥/ m (scale s) {{scale-nz s}})
                 (trans (↧neg (halfUlpᵘ s))
                    (trans (↧/ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}) (pos-2* (scale s)))))
              (cong₂ _*_ (trans (↥neg (halfUlpᵘ s)) (cong -_ (↥/ (+ 1) (2 ℕ.* scale s) {{twice-nz s}})))
                 (↧/ m (scale s) {{scale-nz s}})))
       (lo-num-eq m (+ scale s)))

  -- `m/10^s + 1/(2·10^s)` has numerator `m·2S + S`.
  ↥hi : ∀ m s → ↥ (digitᵘ m s ℚᵘ.+ halfUlpᵘ s)
                  ≡ m * (+ 2 * + scale s) + + 1 * + scale s
  ↥hi m s = trans (↥+ (digitᵘ m s) (halfUlpᵘ s))
    (cong₂ _+_
       (cong₂ _*_ (↥/ m (scale s) {{scale-nz s}})
          (trans (↧/ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}) (pos-2* (scale s))))
       (cong₂ _*_ (↥/ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}) (↧/ m (scale s) {{scale-nz s}})))

  -- Both ends of the window have denominator `S·2S`.
  ↧lo : ∀ m s → ↧ (digitᵘ m s ℚᵘ.- halfUlpᵘ s) ≡ + scale s * (+ 2 * + scale s)
  ↧lo m s = trans (↧+ (digitᵘ m s) (ℚᵘ.- halfUlpᵘ s))
    (cong₂ _*_ (↧/ m (scale s) {{scale-nz s}})
       (trans (↧neg (halfUlpᵘ s))
          (trans (↧/ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}) (pos-2* (scale s)))))

  -- See `↧lo`.
  ↧hi : ∀ m s → ↧ (digitᵘ m s ℚᵘ.+ halfUlpᵘ s) ≡ + scale s * (+ 2 * + scale s)
  ↧hi m s = trans (↧+ (digitᵘ m s) (halfUlpᵘ s))
    (cong₂ _*_ (↧/ m (scale s) {{scale-nz s}})
       (trans (↧/ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}) (pos-2* (scale s))))

------------------------------------------------------------------------
-- Integer inequalities: scaling by a positive and negating

private
  -- `+ P` is positive when `P` is non-zero.
  posℤ : ∀ P .{{_ : ℕ.NonZero P}} → ℤ.Positive (+ P)
  posℤ (suc _) = _

  -- `+ P` is non-negative.
  nonNegℤ : ∀ P → ℤ.NonNegative (+ P)
  nonNegℤ _ = _

  -- Multiplying both sides by a positive `+ P` changes nothing.
  scale≤ : ∀ A B P .{{_ : ℕ.NonZero P}} → (A ℤ.≤ B) ⇔ (A * + P ℤ.≤ B * + P)
  scale≤ A B P = mk⇔ (ℤₚ.*-monoʳ-≤-nonNeg (+ P) {{nonNegℤ P}})
                     (ℤₚ.*-cancelʳ-≤-pos A B (+ P) {{posℤ P}})

  -- …for the strict order too.
  scale< : ∀ A B P .{{_ : ℕ.NonZero P}} → (A ℤ.< B) ⇔ (A * + P ℤ.< B * + P)
  scale< A B P = mk⇔ (ℤₚ.*-monoʳ-<-pos (+ P) {{posℤ P}})
                     (ℤₚ.*-cancelʳ-<-nonNeg (+ P) {{nonNegℤ P}})

  -- Negation reverses `≤`.
  neg≤ : ∀ A B → (A ℤ.≤ B) ⇔ (- B ℤ.≤ - A)
  neg≤ A B = mk⇔ ℤₚ.neg-mono-≤ ℤₚ.neg-cancel-≤

  -- Negation reverses `<`.
  neg< : ∀ A B → (A ℤ.< B) ⇔ (- B ℤ.< - A)
  neg< A B = mk⇔ ℤₚ.neg-mono-< ℤₚ.neg-cancel-<

  -- Rewriting both sides by equations.
  ≡≤ : ∀ {A B A′ B′} → A ≡ A′ → B ≡ B′ → (A ℤ.≤ B) ⇔ (A′ ℤ.≤ B′)
  ≡≤ refl refl = mk⇔ (λ x → x) (λ x → x)

  -- See `≡≤`.
  ≡< : ∀ {A B A′ B′} → A ≡ A′ → B ≡ B′ → (A ℤ.< B) ⇔ (A′ ℤ.< B′)
  ≡< refl refl = mk⇔ (λ x → x) (λ x → x)

  -- ℚᵘ's `≤` is cross-multiplication.
  unfold≤ : ∀ p q → (p ℚᵘ.≤ q) ⇔ (↥ p * ↧ q ℤ.≤ ↥ q * ↧ p)
  unfold≤ p q = mk⇔ (λ where (ℚᵘ.*≤* x) → x) ℚᵘ.*≤*

  -- ℚᵘ's `<` is cross-multiplication.
  unfold< : ∀ p q → (p ℚᵘ.< q) ⇔ (↥ p * ↧ q ℤ.< ↥ q * ↧ p)
  unfold< p q = mk⇔ (λ where (ℚᵘ.*<* x) → x) ℚᵘ.*<*

------------------------------------------------------------------------
-- The four bounds

private
  e₁ : ∀ m D S → (m * (+ 2 * S) - S) * D ≡ (+ 2 * m * D - D) * S
  e₁ = solve-∀

  e₂ : ∀ n S → n * (S * (+ 2 * S)) ≡ (+ 2 * (n * S)) * S
  e₂ = solve-∀

  e₃ : ∀ m D S → (m * (+ 2 * S) + + 1 * S) * D ≡ (+ 2 * m * D + D) * S
  e₃ = solve-∀

  e₄ : ∀ m D S → (m * (+ 2 * S) - S) * D ≡ (- (+ 2 * (- m) * D + D)) * S
  e₄ = solve-∀

  e₅ : ∀ K S → (- K) * (S * (+ 2 * S)) ≡ (- (+ 2 * (K * S))) * S
  e₅ = solve-∀

  e₆ : ∀ m D S → (m * (+ 2 * S) + + 1 * S) * D ≡ (- (+ 2 * (- m) * D - D)) * S
  e₆ = solve-∀

-- The integer spec at an arbitrary scale `S`, so `pow10 s` can be rewritten.
HalfUpAt : ℤ → ℤ → ℤ → ℤ → Set
HalfUpAt n D S m = (+ 2 * m * D - D ℤ.≤ + 2 * (n * S))
                 × (+ 2 * (n * S) ℤ.< + 2 * m * D + D)

private
  -- The integer spec at scale `pow10 s` is the one at `+ 10^s`.
  at-scale : ∀ n d s m → IsRoundHalfUp n d s m ≡ HalfUpAt n +[1+ d ] (+ scale s) m
  at-scale n d s m = cong (λ S → HalfUpAt n +[1+ d ] S m) (pow10≡ s)

  -- Lower bound, non-strict (x ≥ 0 side).
  lo≤ : ∀ n d s m →
        (+ 2 * m * +[1+ d ] - +[1+ d ] ℤ.≤ + 2 * (n * + scale s))
        ⇔ (digitᵘ m s ℚᵘ.- halfUlpᵘ s ℚᵘ.≤ n ℚᵘ./ suc d)
  lo≤ n d s m =
    scale≤ _ _ (scale s) {{scale-nz s}}
    ⟫ ≡≤ (sym (e₁ m +[1+ d ] (+ scale s))) (sym (e₂ n (+ scale s)))
    ⟫ ≡≤ (cong (_* +[1+ d ]) (sym (↥lo m s))) (cong (n *_) (sym (↧lo m s)))
    ⟫ flip⇔ (unfold≤ (digitᵘ m s ℚᵘ.- halfUlpᵘ s) (n ℚᵘ./ suc d))

  -- Upper bound, strict (x ≥ 0 side).
  hi< : ∀ n d s m →
        (+ 2 * (n * + scale s) ℤ.< + 2 * m * +[1+ d ] + +[1+ d ])
        ⇔ (n ℚᵘ./ suc d ℚᵘ.< digitᵘ m s ℚᵘ.+ halfUlpᵘ s)
  hi< n d s m =
    scale< _ _ (scale s) {{scale-nz s}}
    ⟫ ≡< (sym (e₂ n (+ scale s))) (sym (e₃ m +[1+ d ] (+ scale s)))
    ⟫ ≡< (cong (n *_) (sym (↧hi m s))) (cong (_* +[1+ d ]) (sym (↥hi m s)))
    ⟫ flip⇔ (unfold< (n ℚᵘ./ suc d) (digitᵘ m s ℚᵘ.+ halfUlpᵘ s))

  -- Lower bound, strict (x < 0 side), from the mirrored integer upper bound.
  lo< : ∀ k d s m →
        (+ 2 * (+[1+ k ] * + scale s) ℤ.< + 2 * (- m) * +[1+ d ] + +[1+ d ])
        ⇔ (digitᵘ m s ℚᵘ.- halfUlpᵘ s ℚᵘ.< -[1+ k ] ℚᵘ./ suc d)
  lo< k d s m =
    neg< _ _
    ⟫ scale< _ _ (scale s) {{scale-nz s}}
    ⟫ ≡< (sym (e₄ m +[1+ d ] (+ scale s))) (sym (e₅ +[1+ k ] (+ scale s)))
    ⟫ ≡< (cong (_* +[1+ d ]) (sym (↥lo m s))) (cong (-[1+ k ] *_) (sym (↧lo m s)))
    ⟫ flip⇔ (unfold< (digitᵘ m s ℚᵘ.- halfUlpᵘ s) (-[1+ k ] ℚᵘ./ suc d))

  -- Upper bound, non-strict (x < 0 side), from the mirrored integer lower bound.
  hi≤ : ∀ k d s m →
        (+ 2 * (- m) * +[1+ d ] - +[1+ d ] ℤ.≤ + 2 * (+[1+ k ] * + scale s))
        ⇔ (-[1+ k ] ℚᵘ./ suc d ℚᵘ.≤ digitᵘ m s ℚᵘ.+ halfUlpᵘ s)
  hi≤ k d s m =
    neg≤ _ _
    ⟫ scale≤ _ _ (scale s) {{scale-nz s}}
    ⟫ ≡≤ (sym (e₅ +[1+ k ] (+ scale s))) (sym (e₆ m +[1+ d ] (+ scale s)))
    ⟫ ≡≤ (cong (-[1+ k ] *_) (sym (↧hi m s))) (cong (_* +[1+ d ]) (sym (↥hi m s)))
    ⟫ flip⇔ (unfold≤ (-[1+ k ] ℚᵘ./ suc d) (digitᵘ m s ℚᵘ.+ halfUlpᵘ s))

  -- The sign of `n/(d+1)` read with ℚᵘ's order.
  nonneg : ∀ k d → ℚᵘ.0ℚᵘ ℚᵘ.≤ + k ℚᵘ./ suc d
  nonneg k d = ℚᵘₚ.nonNegative⁻¹ (+ k ℚᵘ./ suc d)

  -- A non-negative numerator is never below zero.
  not-neg : ∀ k d → ¬ (+ k ℚᵘ./ suc d ℚᵘ.< ℚᵘ.0ℚᵘ)
  not-neg k d x<0 = ℚᵘₚ.<⇒≱ x<0 (nonneg k d)

  -- A negative numerator is below zero.
  neg : ∀ k d → -[1+ k ] ℚᵘ./ suc d ℚᵘ.< ℚᵘ.0ℚᵘ
  neg k d = ℚᵘ.*<* ℤ.-<+

  -- …and so not at or above it.
  not-nonneg : ∀ k d → ¬ (ℚᵘ.0ℚᵘ ℚᵘ.≤ -[1+ k ] ℚᵘ./ suc d)
  not-nonneg k d = ℚᵘₚ.<⇒≱ (neg k d)

------------------------------------------------------------------------
-- R-DR-3 over ℚᵘ

private
  -- Reads an equation between propositions as an equivalence.
  ≡⇔ : ∀ {A B : Set} → A ≡ B → A ⇔ B
  ≡⇔ refl = mk⇔ (λ x → x) (λ x → x)

-- The integer spec is exactly rounding under ℚᵘ's arithmetic and order.
adequacyᵘ : ∀ n d s m → IsRoundHalfAway n d s m ⇔ RoundsHalfAwayᵘ (n ℚᵘ./ suc d) s m
adequacyᵘ (+ k) d s m =
  ≡⇔ (at-scale (+ k) d s m) ⟫ mk⇔ to from
  where
    to : _ → _
    to (lo , hi) = (λ _ → Equivalence.to (lo≤ (+ k) d s m) lo
                         , Equivalence.to (hi< (+ k) d s m) hi)
                 , (λ x<0 → ⊥-elim (not-neg k d x<0))
    from : _ → _
    from (nonneg-side , _) =
        Equivalence.from (lo≤ (+ k) d s m) (proj₁ (nonneg-side (nonneg k d)))
      , Equivalence.from (hi< (+ k) d s m) (proj₂ (nonneg-side (nonneg k d)))
adequacyᵘ -[1+ k ] d s m =
  ≡⇔ (at-scale +[1+ k ] d s (- m)) ⟫ mk⇔ to from
  where
    to : _ → _
    to (lo , hi) = (λ 0≤x → ⊥-elim (not-nonneg k d 0≤x))
                 , (λ _ → Equivalence.to (lo< k d s m) hi
                        , Equivalence.to (hi≤ k d s m) lo)
    from : _ → _
    from (_ , neg-side) =
        Equivalence.from (hi≤ k d s m) (proj₂ (neg-side (neg k d)))
      , Equivalence.from (lo< k d s m) (proj₁ (neg-side (neg k d)))

------------------------------------------------------------------------
-- R-DR-3 over normalised ℚ

private
  -- Building a normalised rational from `n / P` and reading it back is
  -- equivalent to `n / P` itself.
  toℚᵘ-/ : ∀ n P .{{_ : ℕ.NonZero P}} → ℚ.toℚᵘ (n ℚ./ P) ≃ n ℚᵘ./ P
  toℚᵘ-/ n (suc p) = ℚₚ.toℚᵘ-fromℚᵘ (n ℚᵘ./ suc p)

  -- `toℚᵘ` carries ℚ's `≤` to ℚᵘ's, up to equivalent images.
  transfer≤ : ∀ {p q p′ q′} → ℚ.toℚᵘ p ≃ p′ → ℚ.toℚᵘ q ≃ q′ → (p ℚ.≤ q) ⇔ (p′ ℚᵘ.≤ q′)
  transfer≤ ep eq = mk⇔
    (λ p≤q → ℚᵘₚ.≤-respʳ-≃ eq (ℚᵘₚ.≤-respˡ-≃ ep (ℚₚ.toℚᵘ-mono-≤ p≤q)))
    (λ p′≤q′ → ℚₚ.toℚᵘ-cancel-≤
       (ℚᵘₚ.≤-respʳ-≃ (ℚᵘₚ.≃-sym eq) (ℚᵘₚ.≤-respˡ-≃ (ℚᵘₚ.≃-sym ep) p′≤q′)))

  -- `toℚᵘ` carries ℚ's `<` to ℚᵘ's, up to equivalent images.
  transfer< : ∀ {p q p′ q′} → ℚ.toℚᵘ p ≃ p′ → ℚ.toℚᵘ q ≃ q′ → (p ℚ.< q) ⇔ (p′ ℚᵘ.< q′)
  transfer< ep eq = mk⇔
    (λ p<q → ℚᵘₚ.<-respʳ-≃ eq (ℚᵘₚ.<-respˡ-≃ ep (ℚₚ.toℚᵘ-mono-< p<q)))
    (λ p′<q′ → ℚₚ.toℚᵘ-cancel-<
       (ℚᵘₚ.<-respʳ-≃ (ℚᵘₚ.≃-sym eq) (ℚᵘₚ.<-respˡ-≃ (ℚᵘₚ.≃-sym ep) p′<q′)))

  -- The lower end of the window, read back.
  lo≃ : ∀ m s → ℚ.toℚᵘ (digitℚ m s ℚ.- halfUlpℚ s) ≃ digitᵘ m s ℚᵘ.- halfUlpᵘ s
  lo≃ m s = ℚᵘₚ.≃-trans (ℚₚ.toℚᵘ-homo-+ (digitℚ m s) (ℚ.- halfUlpℚ s))
    (ℚᵘₚ.+-cong (toℚᵘ-/ m (scale s) {{scale-nz s}})
      (ℚᵘₚ.≃-trans (ℚₚ.toℚᵘ-homo‿- (halfUlpℚ s))
        (ℚᵘₚ.-‿cong (toℚᵘ-/ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}))))

  -- The upper end of the window, read back.
  hi≃ : ∀ m s → ℚ.toℚᵘ (digitℚ m s ℚ.+ halfUlpℚ s) ≃ digitᵘ m s ℚᵘ.+ halfUlpᵘ s
  hi≃ m s = ℚᵘₚ.≃-trans (ℚₚ.toℚᵘ-homo-+ (digitℚ m s) (halfUlpℚ s))
    (ℚᵘₚ.+-cong (toℚᵘ-/ m (scale s) {{scale-nz s}}) (toℚᵘ-/ (+ 1) (2 ℕ.* scale s) {{twice-nz s}}))

  -- Implications between equivalent propositions are equivalent.
  →⇔ : ∀ {A A′ B B′ : Set} → A ⇔ A′ → B ⇔ B′ → (A → B) ⇔ (A′ → B′)
  →⇔ a b = mk⇔ (λ f a′ → Equivalence.to b (f (Equivalence.from a a′)))
               (λ g x → Equivalence.from b (g (Equivalence.to a x)))

-- The ℚ statement and the ℚᵘ statement agree on any `x` whose image is `x′`.
RoundsHalfAway-transfer : ∀ {x x′} s m → ℚ.toℚᵘ x ≃ x′ →
                          RoundsHalfAwayℚ x s m ⇔ RoundsHalfAwayᵘ x′ s m
RoundsHalfAway-transfer s m ex =
  →⇔ (transfer≤ ℚᵘₚ.≃-refl ex) (transfer≤ (lo≃ m s) ex ×⇔ transfer< ex (hi≃ m s))
  ×⇔ →⇔ (transfer< ex ℚᵘₚ.≃-refl) (transfer< (lo≃ m s) ex ×⇔ transfer≤ ex (hi≃ m s))

-- The integer spec is exactly rounding under normalised ℚ's arithmetic and order.
adequacyℚ : ∀ n d s m → IsRoundHalfAway n d s m ⇔ RoundsHalfAwayℚ (n ℚ./ suc d) s m
adequacyℚ n d s m =
  adequacyᵘ n d s m ⟫ flip⇔ (RoundsHalfAway-transfer s m (toℚᵘ-/ n (suc d)))

------------------------------------------------------------------------
-- What this buys for the shipped function

-- The digit `roundHalfAway` computes is `n/(d+1)` rounded to `s` places,
-- read with normalised ℚ's arithmetic and order.
roundHalfAway-roundsℚ : ∀ n d s → RoundsHalfAwayℚ (n ℚ./ suc d) s (roundHalfAway n d s)
roundHalfAway-roundsℚ n d s =
  Equivalence.to (adequacyℚ n d s (roundHalfAway n d s)) (roundHalfAway-sound n d s)

-- …and it is the only digit that is.
roundsℚ-unique : ∀ {n d s m} → RoundsHalfAwayℚ (n ℚ./ suc d) s m → m ≡ roundHalfAway n d s
roundsℚ-unique {n} {d} {s} {m} r =
  unique-halfAway {n} {d} {s} (Equivalence.from (adequacyℚ n d s m) r)
                  (roundHalfAway-sound n d s)

-- A known answer through the whole chain: −0.125 to two places is −0.13,
-- an exact half sent away from zero.
neg-tie-roundsℚ : RoundsHalfAwayℚ (-[1+ 0 ] ℚ./ 8) 2 -[1+ 12 ]
neg-tie-roundsℚ = roundHalfAway-roundsℚ -[1+ 0 ] 7 2
