-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- The hypergeometric law of a 2×2 table with fixed margins, as integers.
--
--                 col 1     col 2
--        row 1      a       m − a      | m
--        row 2    k − a   n − (k − a)  | n
--                   k                  | m + n
--
-- Given the margins, the table is fixed by a = cell (1,1).  Its probability under
-- independence is weight m n k a / total m n k, where the weight is
-- C(m, a) · C(n, k − a) and the total is C(m + n, k).  Working with the integer
-- numerator and denominator keeps every statement exact, and it is exactly what
-- the Julia code computes (in BigInt) before forming one Rational at the end.

{-# OPTIONS --without-K --safe #-}

module ExactTests.Hypergeometric where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open import ExactTests.Sums
open import ExactTests.Binomial

weight : ℕ → ℕ → ℕ → ℕ → ℕ
weight m n k a = C m a * C n (k ∸ a)

total : ℕ → ℕ → ℕ → ℕ
total m n k = C (m + n) k

-- The weights of all tables with these margins sum to the total: the pmf sums to 1.
weights-sum : ∀ m n k → sumTo k (weight m n k) ≡ total m n k
weights-sum = vandermonde

-- A table whose four cells are non-negative has positive weight.
-- (a ≤ k, so k − a is the true cell (2,1); the other two cells are m − a and
--  n − (k − a), non-negative exactly when a ≤ m and k − a ≤ n.)
weight-pos : ∀ {m n k a} → a ≤ m → k ∸ a ≤ n → 0 < weight m n k a
weight-pos a≤m ka≤n = *-mono-≤ (C-pos a≤m) (C-pos ka≤n)

-- The total is positive whenever any table exists.
total-pos : ∀ {m n k a} → a ≤ k → a ≤ m → k ∸ a ≤ n → 0 < total m n k
total-pos {m} {n} {k} {a} a≤k a≤m ka≤n =
  ≤-trans (weight-pos {m} {n} {k} {a} a≤m ka≤n)
          (≤-trans (term-≤-sumTo k (weight m n k) a≤k) (≤-reflexive (weights-sum m n k)))
