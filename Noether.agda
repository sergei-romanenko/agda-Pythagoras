module Noether where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Agda.Primitive
open import Data.Product
open import Relation.Binary.Core
open import Relation.Nullary
open import Relation.Unary

Noether : ∀ {a l} -> (A : Set a) -> (R : Rel A l) -> Set (lsuc l ⊔ a)
Noether {_} {l} A R 
  = (P : Pred A l) -> 
    ((x : A) -> ((y : A) -> R y x -> P y) -> P x) -> (z : A) -> P z

-- The principle of infinite descent, following Fermat
-- http://en.wikipedia.org/wiki/Infinite_descent
infiniteDescent : ∀ {a l} -> (A : Set a) -> (R : Rel A l) ->
                  (P : Pred A l) -> Noether A R -> 
                  ((x : A) -> P x -> ∃ (λ y -> R y x × P y)) -> 
                  (z : A) -> ¬ (P z)
infiniteDescent A R P noe f
    = noe (λ w → ¬ P w) g
      where g : (x : A) → ((y : A) → R y x → ¬ P y) → ¬ P x 
            g x h px with f x px
            ... | (v , k) = h v (proj₁ k) (proj₂ k)

-- original proofs
{-
∃-elim : ∀ {a b c} -> {A : Set a} -> {B : A -> Set b} -> {C : Set c}
          (f : ∃ B) -> (g : (x : A) -> B x -> C) -> C
∃-elim (proj₁ , proj₂) g = g proj₁ proj₂

×-elimLeft : ∀ {a b} -> {A : Set a} -> {B : Set b} -> A × B -> A
×-elimLeft (proj₁ , proj₂) = proj₁

×-elimRight : ∀ {a b} -> {A : Set a} -> {B : Set b} -> A × B -> B
×-elimRight (proj₁ , proj₂) = proj₂

infiniteDescent A R P h1 h2 x 
  = h1 (λ y → ¬ P y) 
       ((λ (z : A) (h3 : (y : A) → R y z → ¬ P y) (h4 : P z) → 
           ∃-elim (h2 z h4) 
                   (λ (y : A) (h5 : R y z × P y) → 
                      h3 y (×-elimLeft h5) (×-elimRight h5))))
       x
-}

