module Noether where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Agda.Primitive
open import Data.Product
open import Data.Empty
open import Relation.Binary.Core
open import Relation.Nullary
open import Relation.Unary

open import Function

Noether : ∀ {a l} (A : Set a) (_>_ : Rel A l) → Set (lsuc l ⊔ a)
Noether {_} {l} A _>_ =
  (P : Pred A l) → 
  (∀ x → (∀ y → y > x → P y) → P x) → ∀ z → P z

-- The principle of infinite descent, following Fermat
-- http://en.wikipedia.org/wiki/Infinite_descent
infiniteDescent : ∀ {a l} (A : Set a) (_>_ : Rel A l) (P : Pred A l) →
                  Noether A _>_ → 
                  (∀ x → P x → ∃ (λ y → y > x × P y)) → 
                  ∀ z → ¬ (P z)
infiniteDescent A _>_ P noe f =
  noe (¬_ ∘  P) helper
  where helper : ∀ x → (∀ y → y > x → ¬ P y) → ¬ P x
        helper x h px with f x px
        ... | y , y>x , py = h y y>x py
