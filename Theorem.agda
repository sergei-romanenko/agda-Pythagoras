open import Agda.Primitive

open import CancellativeAbelianMonoid

module Theorem (a : Level) (m : CancellativeAbelianMonoid a a)
  where

-- it seems important that the two level of CancellativeAbelianMonoid
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

import Lemma
module Q = Lemma a a m
open Q
open import Noether
import Property
module R = Property a a m
open R

-- The main theorem which is originally proved by Thierry Coquand:
-- any prime cannot be a square of rational in cancellative
-- abelian monoid.
-- the main theorem

theorem : ∀ p → Prime p → Noether Carrier (multiple p) → NotSquare p
theorem p prime-p noe x y pxx≈yy
  with infiniteDescent Carrier (multiple p) (Square p) noe (jump-down p prime-p)
... | ¬sq-p
  = ¬sq-p x (y , pxx≈yy)

open import Induction.WellFounded
  using (Acc; acc)

theorem₂ : ∀ p → Prime p → ∀ x u → p ∙ (x ∙ x) ≈ (u ∙ u) →
             Acc (multiple p) u → ⊥
theorem₂ p prime-p x u pxx≈uu (acc rs)
  with step-down p prime-p x u pxx≈uu
... | y , py≈u , pyy≈xx
  with step-down p prime-p y x pyy≈xx
... | w , pw≈x , pww≈yy
  = theorem₂ p prime-p w y pww≈yy (rs y py≈u)
