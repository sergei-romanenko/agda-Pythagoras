open import Relation.Binary

module Cancel {a l} {A : Set a} (_≈_ : Rel A l) where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Algebra.FunctionProperties
open import Level

Cancel : Op₂ A → Set (l ⊔ a)
Cancel _∙_ = ∀ x y z → (z ∙ x) ≈ (z ∙ y) → x ≈ y
