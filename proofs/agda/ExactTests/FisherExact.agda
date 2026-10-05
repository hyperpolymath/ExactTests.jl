-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- Fisher's exact test on a 2×2 table: the p-value is a probability, and it is
-- never zero.
--
-- Each p-value is   tail / total   where tail = Σ over the tables the
-- alternative keeps of their weight.  The three alternatives are R's:
--
--   less       keep a  ⇔  a ≤ x
--   greater    keep a  ⇔  x ≤ a
--   two-sided  keep a  ⇔  weight a · d ≤ weight x · (d + e)
--
-- The two-sided rule is R's `d <= d_obs * (1 + 10^-7)`, written over the integers
-- with relative tolerance e / d.  R's default is e = 1, d = 10^7 (`relErr`).
-- Because Julia evaluates the same inequality on exact integers, the only way the
-- two can differ is R's floating-point evaluation of the weights; the tolerance
-- exists to absorb exactly that.
--
-- Proved for every table with non-negative cells and every tolerance:
--   p-bounds : 0 < tail ≤ total          (so p ∈ (0, 1])
--   two-sided-mono : a larger tolerance never gives a smaller p-value.

{-# OPTIONS --without-K --safe #-}

module ExactTests.FisherExact where

open import Data.Bool.Base using (Bool; T)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality

open import ExactTests.Sums
open import ExactTests.Binomial
open import ExactTests.Hypergeometric

data Alternative : Set where
  two-sided less greater : Alternative

-- R's relative tolerance 1 + e/d is e = 1, d = 10^7.  The lemmas below are
-- generic in (d, e); only `keep` fixes R's values.
rD : ℕ
rD = 10000000

keepTwo : (d e m n k x : ℕ) → ℕ → Bool
keepTwo d e m n k x a = weight m n k a * d ≤ᵇ weight m n k x * (d + e)

keepLess : ℕ → ℕ → Bool
keepLess x a = a ≤ᵇ x

keepGreater : ℕ → ℕ → Bool
keepGreater x a = x ≤ᵇ a

keep : Alternative → (m n k x : ℕ) → ℕ → Bool
keep two-sided m n k x = keepTwo rD 1 m n k x
keep less      m n k x = keepLess x
keep greater   m n k x = keepGreater x

-- The p-value's numerator under the given alternative (denominator: `total`).
tail : Alternative → (m n k x : ℕ) → ℕ
tail alt m n k x = sel (keep alt m n k x) (weight m n k) k

------------------------------------------------------------------------
-- The observed table is always in its own tail.

keepTwo-self : ∀ d e m n k x → T (keepTwo d e m n k x x)
keepTwo-self d e m n k x = ≤⇒≤ᵇ (*-monoʳ-≤ (weight m n k x) (m≤m+n d e))

keep-self : ∀ alt m n k x → T (keep alt m n k x x)
keep-self two-sided m n k x = keepTwo-self rD 1 m n k x
keep-self less      m n k x = ≤⇒≤ᵇ (≤-refl {x})
keep-self greater   m n k x = ≤⇒≤ᵇ (≤-refl {x})

------------------------------------------------------------------------
-- p ∈ (0, 1]

-- A valid observed table: x ≤ k (cell (2,1) is k − x), x ≤ m, k − x ≤ n.
record Valid (m n k x : ℕ) : Set where
  field
    x≤k  : x ≤ k
    x≤m  : x ≤ m
    kx≤n : k ∸ x ≤ n

p-pos : ∀ alt {m n k x} → Valid m n k x → 0 < tail alt m n k x
p-pos alt {m} {n} {k} {x} v =
  ≤-trans (weight-pos {m} {n} {k} {x} (Valid.x≤m v) (Valid.kx≤n v))
          (sel-member (keep alt m n k x) (weight m n k) k (Valid.x≤k v) (keep-self alt m n k x))

p-≤-1 : ∀ alt m n k x → tail alt m n k x ≤ total m n k
p-≤-1 alt m n k x =
  ≤-trans (sel-≤ (keep alt m n k x) (weight m n k) k) (≤-reflexive (weights-sum m n k))

p-bounds : ∀ alt {m n k x} → Valid m n k x → 0 < tail alt m n k x × tail alt m n k x ≤ total m n k
p-bounds alt {m} {n} {k} {x} v = p-pos alt v , p-≤-1 alt m n k x

------------------------------------------------------------------------
-- The two-sided p-value is monotone in the tolerance.

keepTwo-mono : ∀ d {e e′} m n k x → e ≤ e′ → ∀ a → T (keepTwo d e m n k x a) → T (keepTwo d e′ m n k x a)
keepTwo-mono d {e} {e′} m n k x e≤e′ a h =
  ≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ (weight m n k a * d) (weight m n k x * (d + e)) h) (*-monoʳ-≤ (weight m n k x) (+-monoʳ-≤ d e≤e′)))

two-sided-mono : ∀ d {e e′} m n k x → e ≤ e′ →
  sel (keepTwo d e m n k x) (weight m n k) k ≤ sel (keepTwo d e′ m n k x) (weight m n k) k
two-sided-mono d {e} {e′} m n k x e≤e′ =
  sel-mono (keepTwo d e m n k x) (keepTwo d e′ m n k x) (weight m n k) k (keepTwo-mono d m n k x e≤e′)
