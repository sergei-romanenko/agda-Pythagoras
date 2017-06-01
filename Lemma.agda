open import Agda.Primitive

import CancellativeAbelianMonoid

module Lemma
  (a l : Level) (cam : CancellativeAbelianMonoid.CancellativeAbelianMonoid a l)
  where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Data.Product
open import Data.Sum as Sum
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR

open import Function
  using (_∘_; _$_; id)
import Function.Related as Related

import Property
open Property a l cam

open EqR (≈-setoid)

p∣sq : ∀ p x → Prime p → p divides (x ∙ x) → p divides x
p∣sq p x pr-p p∣xx = [ id , id ]′ $ pr-p x x p∣xx

step-down : ∀ p x y → Prime p → p ∙ (x ∙ x) ≈ (y ∙ y) →
          ∃ (λ z → (p ∙ z ≈ y) × (p ∙ (z ∙ z) ≈ (x ∙ x)))
step-down p x y p-pr pxx≈yy
  with p∣sq p y p-pr ((x ∙ x) , pxx≈yy)
... | w , pw≈y = w , pw≈y , ∙-cancel (p ∙ (w ∙ w)) (x ∙ x) p help
  where
  help : p ∙ (p ∙ (w ∙ w)) ≈ p ∙ (x ∙ x)
  help = begin
    p ∙ (p ∙ (w ∙ w))
      ≈⟨ ∙-cong ≈-refl
         (begin
           p ∙ (w ∙ w)
             ≈⟨ ≈-sym $ ∙-assoc p w w ⟩
           (p ∙ w) ∙ w
             ≈⟨ ∙-comm (p ∙ w) w ⟩
           w ∙ (p ∙ w)
         ∎) ⟩
    p ∙ (w ∙ (p ∙ w))
      ≈⟨ ≈-sym $ ∙-assoc p w (p ∙ w) ⟩
    (p ∙ w) ∙ (p ∙ w)
      ≈⟨ ∙-cong pw≈y pw≈y ⟩
    y ∙ y
      ≈⟨ ≈-sym $ pxx≈yy ⟩
    p ∙ (x ∙ x)
    ∎

jump-down : ∀ p → Prime p → ∀ x → (∃ λ u → p ∙ (x ∙ x) ≈ u ∙ u) → 
          ∃ λ z → (p ∙ z ≈ x) × (∃ λ w → p ∙ (z ∙ z) ≈ w ∙ w)
jump-down p pr-p x (u , pxx≈uu)
  with step-down p x u pr-p pxx≈uu
... | w , pw≈u , pww≈xx
  with step-down p w x pr-p pww≈xx
... | z , pz≈x , pzz≈ww =
  z , pz≈x , w , pzz≈ww
