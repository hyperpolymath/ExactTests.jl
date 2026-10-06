-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- MUST FAIL: `--safe` (from exacttests-proofs.agda-lib and the gate's command
-- line, deliberately not repeated in this file) forbids postulates.  Guards
-- against the library flags being dropped: if this file ever type-checks, a
-- postulate anywhere in the tree would too.
-- EXPECT: Cannot postulate every-natural-is-zero with safe flag

module reject.Postulate where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

postulate every-natural-is-zero : (n : ℕ) → n ≡ 0
