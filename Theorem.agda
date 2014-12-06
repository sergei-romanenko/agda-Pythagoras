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
open import Relation.Binary
open import Relation.Nullary
open import Relation.Unary

import Lemma
module Q = Lemma a a m
open Q
open import Noether
import Property
module R = Property a a m
open R

-- the main theorem
theorem : (p : Carrier) -> (p isPrime) -> Noether Carrier (multiple p) -> 
          (p isNotSquare)
theorem p h1 h2
  = let rem : (z : Carrier) → ¬ Square p z
        rem = infiniteDescent Carrier (multiple p) (Square p) h2 (lemma9 p h1)
    in λ x y h3 → rem x (y , h3)
