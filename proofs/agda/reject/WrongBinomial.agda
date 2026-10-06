-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL: C(2, 1) is 2, not 1.  Guards against the type-checker not
-- evaluating `C` at all: Pascal's rule must compute, or every closed identity
-- about the weights is unverified.
-- EXPECT: 2 != 1 of type

{-# OPTIONS --without-K --safe #-}

module reject.WrongBinomial where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ExactTests.Binomial using (C)

two-choose-one : C 2 1 ≡ 1
two-choose-one = refl
