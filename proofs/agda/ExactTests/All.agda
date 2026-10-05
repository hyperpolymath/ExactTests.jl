-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- The gate entry point.  `proofs/check.sh` type-checks this module, and the
-- axiom audit fails any `.agda` file under `ExactTests/` not reachable from it:
-- a module nobody imports here is a module nobody checks.

{-# OPTIONS --without-K --safe #-}

module ExactTests.All where

import ExactTests.Sums
import ExactTests.Binomial
import ExactTests.Hypergeometric
import ExactTests.FisherExact
