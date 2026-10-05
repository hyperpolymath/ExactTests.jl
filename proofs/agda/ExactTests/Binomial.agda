-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Binomial coefficients by Pascal's rule, and Vandermonde's identity
--
--   Σ_{a=0}^{k} C(m, a) · C(n, k − a) = C(m + n, k).
--
-- `C` is defined by Pascal's rule, not by factorials, so the rule holds by
-- computation and C(n, k) = 0 for k > n needs no division.  Vandermonde is what
-- makes the hypergeometric weights a probability distribution: the weights of
-- all 2×2 tables with fixed margins sum to the normaliser.

{-# OPTIONS --without-K --safe #-}

module ExactTests.Binomial where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import ExactTests.Sums

C : ℕ → ℕ → ℕ
C n       zero    = 1
C zero    (suc k) = 0
C (suc n) (suc k) = C n k + C n (suc k)

-- C(n, k) > 0 inside the triangle.
C-pos : ∀ {n k} → k ≤ n → 0 < C n k
C-pos {n}     {zero}  _         = s≤s z≤n
C-pos {suc n} {suc k} (s≤s k≤n) = ≤-trans (C-pos k≤n) (m≤m+n (C n k) (C n (suc k)))

-- C(n, k) = 0 outside it.
C-zero : ∀ {n k} → n < k → C n k ≡ 0
C-zero {zero}  {suc k} _         = refl
C-zero {suc n} {suc k} (s≤s n<k) = cong₂ _+_ (C-zero n<k) (C-zero (≤-trans n<k (n≤1+n k)))

vandermonde : ∀ m n k → conv (C m) (C n) k ≡ C (m + n) k
vandermonde zero    n zero    = refl
vandermonde zero    n (suc k) =
  trans (cong₂ _+_ (*-identityˡ (C n (suc k))) (sumTo-zero k _ (λ _ → refl)))
        (+-identityʳ (C n (suc k)))
vandermonde (suc m) n zero    = refl
vandermonde (suc m) n (suc k) = begin
  A + sumTo k (λ a → (C m a + C m (suc a)) * C n (k ∸ a))
    ≡⟨ cong (A +_) (sumTo-cong k (λ a → *-distribʳ-+ (C n (k ∸ a)) (C m a) (C m (suc a)))) ⟩
  A + sumTo k (λ a → C m a * C n (k ∸ a) + C m (suc a) * C n (k ∸ a))
    ≡⟨ cong (A +_) (sumTo-+ k _ _) ⟩
  A + (conv (C m) (C n) k + conv (C m ∘ suc) (C n) k)
    ≡⟨ swap-+ A (conv (C m) (C n) k) (conv (C m ∘ suc) (C n) k) ⟩
  conv (C m) (C n) k + conv (C m) (C n) (suc k)
    ≡⟨ cong₂ _+_ (vandermonde m n k) (vandermonde m n (suc k)) ⟩
  C (m + n) k + C (m + n) (suc k) ∎
  where
  open ≡-Reasoning
  A = 1 * C n (suc k)
