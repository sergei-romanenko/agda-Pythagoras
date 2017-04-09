module README where

-- 2 is prime: a short proof by Danielsson.
import 2IsPrime

-- The definitions of Noetherian and Fermat's infinite descent principle.
import Noether

-- The definition of cancel.
import Cancel

-- The definition of cancellative abelian monoid.
import CancellativeAbelianMonoid

-- Helper functions of a cancellative abelian monoid.
import Property

-- A lemma for the proof of the main theorem in `Theorem.agda`.
import Lemma

-- A set of natural numbers without zero, and its multiplication.
import NatStar
-- Properties of NatStar.
import NatStarProperties
-- The main theorem which is originally proved by Thierry Coquand:
-- any prime cannot be a square of rational in cancellative
-- abelian monoid.
import Theorem

import Corollary
