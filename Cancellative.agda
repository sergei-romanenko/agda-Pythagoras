module Cancellative where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Agda.Primitive
open import Algebra
  using (CommutativeMonoid)
open import Algebra.Structures
  using (IsCommutativeMonoid)
open import Algebra.FunctionProperties.Core
  using (Op₂)
import Algebra.FunctionProperties
open import Relation.Binary
  using (Rel)

module _ {a l} {A : Set a} (_≈_ : Rel A l) (_∙_ : Op₂ A) where

  Cancel : Set (l ⊔ a)
  Cancel = ∀ x y z → (z ∙ x) ≈ (z ∙ y) → x ≈ y

record IsCancellativeAbelianMonoid 
  {a l} {A : Set a} (≈ : Rel A l) (_∙_ : Op₂ A)
  (ε : A) : Set (a ⊔ l)
  where

  open Algebra.FunctionProperties ≈
  field
    isCommutativeMonoid : IsCommutativeMonoid ≈ _∙_ ε
    cancel : Cancel ≈ _∙_

  open IsCommutativeMonoid isCommutativeMonoid public

record CancellativeAbelianMonoid c l : Set (lsuc (c ⊔ l)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier l
    _∙_     : Op₂ Carrier
    ε       : Carrier
    isCancellativeAbelianMonoid : IsCancellativeAbelianMonoid _≈_ _∙_ ε

  open IsCancellativeAbelianMonoid isCancellativeAbelianMonoid public

  commutativeMonoid : CommutativeMonoid c l
  commutativeMonoid 
    = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public 
    using (setoid; semigroup; rawMonoid; monoid)
