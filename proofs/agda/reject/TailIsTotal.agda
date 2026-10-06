-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL: for the table with margins m = n = k = 1 and observed cell x = 0
-- (rows (0, 1) and (1, 0)), the `less` tail is the one table with a ≤ 0, of
-- weight 1, while the total is C(2, 1) = 2: the p-value is 1/2, not 1.  Guards
-- against `tail` and `total` collapsing into the same quantity, which would make
-- `p-≤-1` true for the wrong reason.
-- EXPECT: 1 != 2 of type

{-# OPTIONS --without-K --safe #-}

module reject.TailIsTotal where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ExactTests.Hypergeometric using (total)
open import ExactTests.FisherExact using (tail; less)

half-is-one : tail less 1 1 1 0 ≡ total 1 1 1
half-is-one = refl
