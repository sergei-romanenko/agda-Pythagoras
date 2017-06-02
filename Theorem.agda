open import Agda.Primitive

open import CancellativeAbelianMonoid

module Theorem (a : Level) (m : CancellativeAbelianMonoid a a)
  where

-- it seems important that the two levels of CancellativeAbelianMonoid
-- should be equal for proof of the theorem as follows.

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Data.Product
open import Data.Empty
open import Relation.Binary
open import Relation.Nullary
open import Relation.Unary

open import Function

open import Induction.WellFounded
  using (Acc; acc)

import Lemma
module Q = Lemma a a m
open Q
import Property
module R = Property a a m
open R

-- The main theorem which is originally proved by Thierry Coquand:
-- any prime cannot be a square of rational in cancellative
-- abelian monoid.

theorem : ∀ p → Prime p → ∀ x u → p ∙ (x ∙ x) ≈ (u ∙ u) →
             Acc (multiple p) u → ⊥
theorem p prime-p x u pxx≈uu (acc rs)
  with step-down p prime-p x u pxx≈uu
... | y , py≈u , pyy≈xx
  with step-down p prime-p y x pyy≈xx
... | w , pw≈x , pww≈yy
  = theorem p prime-p w y pww≈yy (rs y py≈u)
