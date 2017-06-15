open import Agda.Primitive

open import Cancellative

module Theorem (a : Level) (m : CancellativeAbelianMonoid a a) where

-- it seems important that the two levels of CancellativeAbelianMonoid
-- should be equal for proof of the theorem as follows.

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Algebra
open import Algebra.Structures

open import Data.Product
open import Data.Sum as Sum
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_)
open import Relation.Nullary
open import Relation.Unary

open import Function
  using (_∘_; _$_; id)

open import Induction.WellFounded
  using (Acc; acc)
import Relation.Binary.EqReasoning as EqR

open CancellativeAbelianMonoid {a} {a} m public
  renaming ( setoid to ≈-setoid
           ; refl   to ≈-refl
           ; sym    to ≈-sym
           ; trans  to ≈-trans
           ; assoc  to ∙-assoc
           ; ∙-cong to ∙-cong
           ; comm   to ∙-comm
           ; cancel to ∙-cancel
           )

open EqR (≈-setoid)

multiple : (p : Carrier) → Rel Carrier a
multiple p x y = (p ∙ x) ≈ y

_divides_ : Rel Carrier a
x divides y = ∃ λ z → (x ∙ z) ≈ y


Prime : Pred Carrier a
Prime p = ∀ x y → p divides (x ∙ y) →
            p divides x ⊎ p divides y

NotSquare : Pred Carrier a
NotSquare p = ∀ x y → ¬ (p ∙ (x ∙ x) ≈ y ∙ y)

p∣sq : ∀ p x → Prime p → p divides (x ∙ x) → p divides x
p∣sq p x pr-p p∣xx = [ id , id ]′ $ pr-p x x p∣xx

step-down : ∀ p → Prime p → ∀ x y →  p ∙ (x ∙ x) ≈ (y ∙ y) →
          ∃ (λ z → (p ∙ z ≈ y) × (p ∙ (z ∙ z) ≈ (x ∙ x)))
step-down p p-prime x y pxx≈yy
  with p∣sq p y p-prime ((x ∙ x) , pxx≈yy)
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
