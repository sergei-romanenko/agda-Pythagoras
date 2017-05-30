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

----
---- Miscellanea
----

-- There is no m and n such that
--   n ≢ 0 and m^2 ≡ 2*n^2
-- Hence, sqrt 2 is irrational.

-- The proof in Coq has been originally written by Pierre Corbineau
-- http://www-verimag.imag.fr/~corbinea/ftp/programs/sqrt2.v

import Corbineau.Sqrt2

-- 2 is prime.
-- Originally written by Nils Anders Danielsson
-- https://lists.chalmers.se/pipermail/agda/2011/003464.html

import Danielsson.2IsPrime
