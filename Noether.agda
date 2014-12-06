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

-- original proofs
{-
∃-elim : ∀ {a b c} → {A : Set a} → {B : A → Set b} → {C : Set c}
          (f : ∃ B) → (g : (x : A) → B x → C) → C
∃-elim (proj₁ , proj₂) g = g proj₁ proj₂

×-elimLeft : ∀ {a b} → {A : Set a} → {B : Set b} → A × B → A
×-elimLeft (proj₁ , proj₂) = proj₁

×-elimRight : ∀ {a b} → {A : Set a} → {B : Set b} → A × B → B
×-elimRight (proj₁ , proj₂) = proj₂

infiniteDescent A R P h1 h2 x 
  = h1 (λ y → ¬ P y) 
       ((λ (z : A) (h3 : (y : A) → R y z → ¬ P y) (h4 : P z) → 
           ∃-elim (h2 z h4) 
                   (λ (y : A) (h5 : R y z × P y) → 
                      h3 y (×-elimLeft h5) (×-elimRight h5))))
       x
-}

