module README where

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

-- The main theorem which is originally proved by Thierry Coquand:
-- any prime cannot be a square of rational in cancellative
-- abelian monoid.
import Theorem

-- Some properties of ℕ
import 2Divides

-- A set of natural numbers without zero.
import NatPlus

-- The set of the natural numbers without zero and with multiplication
-- forms a cancellative abelian modoid.
-- Thus, the square root of two is irrational.
import Corollary
