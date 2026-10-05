-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Finite sums over ℕ and the few facts about them the tests need.
--
-- `sumTo k f` is f 0 + f 1 + … + f k, peeled from the left, so that the
-- convolution of two sequences unfolds by computation (`conv-suc` is `refl`).
-- Everything is stated pointwise: there is no function extensionality under
-- `--without-K --safe`, so equal summands are passed as `∀ a → f a ≡ g a`.

{-# OPTIONS --without-K --safe #-}

module ExactTests.Sums where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; T)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Definitions

-- Σ_{a=0}^{k} f a.
sumTo : ℕ → (ℕ → ℕ) → ℕ
sumTo zero    f = f 0
sumTo (suc k) f = f 0 + sumTo k (f ∘ suc)

-- The convolution Σ_{a=0}^{k} f a · g (k − a).
conv : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ
conv f g k = sumTo k (λ a → f a * g (k ∸ a))

-- Σ_{a=0}^{k} [keep a] · f a: the part of the sum a test's tail keeps.
sel : (ℕ → Bool) → (ℕ → ℕ) → ℕ → ℕ
sel keep f k = sumTo k (λ a → if keep a then f a else 0)

------------------------------------------------------------------------
-- Arithmetic helper

swap-+ : ∀ a b c → a + (b + c) ≡ b + (a + c)
swap-+ a b c = trans (sym (+-assoc a b c)) (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

------------------------------------------------------------------------
-- Sums

conv-suc : ∀ f g k → conv f g (suc k) ≡ f 0 * g (suc k) + conv (f ∘ suc) g k
conv-suc f g k = refl

sumTo-cong : ∀ k {f g} → (∀ a → f a ≡ g a) → sumTo k f ≡ sumTo k g
sumTo-cong zero    eq = eq 0
sumTo-cong (suc k) eq = cong₂ _+_ (eq 0) (sumTo-cong k (eq ∘ suc))

sumTo-+ : ∀ k f g → sumTo k (λ a → f a + g a) ≡ sumTo k f + sumTo k g
sumTo-+ zero    f g = refl
sumTo-+ (suc k) f g = begin
  (f 0 + g 0) + sumTo k (λ a → f (suc a) + g (suc a))
    ≡⟨ cong ((f 0 + g 0) +_) (sumTo-+ k (f ∘ suc) (g ∘ suc)) ⟩
  (f 0 + g 0) + (F + G)
    ≡⟨ +-assoc (f 0) (g 0) (F + G) ⟩
  f 0 + (g 0 + (F + G))
    ≡⟨ cong (f 0 +_) (swap-+ (g 0) F G) ⟩
  f 0 + (F + (g 0 + G))
    ≡⟨ sym (+-assoc (f 0) F (g 0 + G)) ⟩
  (f 0 + F) + (g 0 + G) ∎
  where
  open ≡-Reasoning
  F = sumTo k (f ∘ suc)
  G = sumTo k (g ∘ suc)

sumTo-zero : ∀ k f → (∀ a → f a ≡ 0) → sumTo k f ≡ 0
sumTo-zero zero    f z = z 0
sumTo-zero (suc k) f z = cong₂ _+_ (z 0) (sumTo-zero k (f ∘ suc) (z ∘ suc))

sumTo-mono : ∀ k {f g} → (∀ a → f a ≤ g a) → sumTo k f ≤ sumTo k g
sumTo-mono zero    le = le 0
sumTo-mono (suc k) le = +-mono-≤ (le 0) (sumTo-mono k (le ∘ suc))

-- Every summand inside the range is at most the sum.
term-≤-sumTo : ∀ k f {x} → x ≤ k → f x ≤ sumTo k f
term-≤-sumTo zero    f z≤n       = ≤-refl
term-≤-sumTo (suc k) f z≤n       = m≤m+n (f 0) (sumTo k (f ∘ suc))
term-≤-sumTo (suc k) f (s≤s x≤k) =
  ≤-trans (term-≤-sumTo k (f ∘ suc) x≤k) (m≤n+m (sumTo k (f ∘ suc)) (f 0))

------------------------------------------------------------------------
-- Selected sums (tails)

if-≤ : ∀ b y → (if b then y else 0) ≤ y
if-≤ true  y = ≤-refl
if-≤ false y = z≤n

if-true : ∀ b y → T b → (if b then y else 0) ≡ y
if-true true y _ = refl

if-mono : ∀ b₁ b₂ y → (T b₁ → T b₂) → (if b₁ then y else 0) ≤ (if b₂ then y else 0)
if-mono false b₂    y _ = z≤n
if-mono true  true  y _ = ≤-refl
if-mono true  false y h = ⊥-elim (h tt)

-- A tail is at most the whole sum.
sel-≤ : ∀ keep f k → sel keep f k ≤ sumTo k f
sel-≤ keep f k = sumTo-mono k (λ a → if-≤ (keep a) (f a))

-- A kept summand inside the range is at most the tail.
sel-member : ∀ keep f k {x} → x ≤ k → T (keep x) → f x ≤ sel keep f k
sel-member keep f k {x} x≤k kx =
  subst (_≤ sel keep f k) (if-true (keep x) (f x) kx)
        (term-≤-sumTo k (λ a → if keep a then f a else 0) x≤k)

-- Keeping more never shrinks the tail.
sel-mono : ∀ keep₁ keep₂ f k → (∀ a → T (keep₁ a) → T (keep₂ a)) → sel keep₁ f k ≤ sel keep₂ f k
sel-mono keep₁ keep₂ f k h = sumTo-mono k (λ a → if-mono (keep₁ a) (keep₂ a) (f a) (h a))
