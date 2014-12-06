open import Level

open import CancellativeAbelianMonoid

module Lemma
  (a l : Level) (m : CancellativeAbelianMonoid a l)
  where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Data.Product
open import Data.Sum
open import Relation.Binary
import Relation.Binary.EqReasoning as EqReasoning

import Property
module P = Property a l m
open P

open EqReasoning (≈-setoid)

⊎-elim : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} -> 
         (A -> C) -> (B -> C) -> A ⊎ B -> C
⊎-elim f g (inj₁ x) = f x
⊎-elim f g (inj₂ y) = g y

∃-elim : ∀ {a b c} {A : Set a} {B : A -> Set b} 
             {C : Set c} ->
          ∃ B -> ((x : A) -> B x -> C) -> C
∃-elim (proj₁ , proj₂) f = f proj₁ proj₂

×-elimLeft : ∀ {a b} (A : Set a) (B : Set b) -> 
               A × B -> A
×-elimLeft A B (proj₁ , proj₂) = proj₁

×-elimRight : ∀ {a b} (A : Set a) (B : Set b) -> 
               A × B -> B
×-elimRight A B (proj₁ , proj₂) = proj₂

-- required by proof of lemma3
assoc' : (x y z : Carrier) -> (x ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ z)
assoc' x y z = ≈-sym (assoc x y z)

∙-congLeft : (x y z : Carrier) -> y ≈ z -> (y ∙ x) ≈ (z ∙ x)
∙-congLeft x y z p = ∙-cong p ≈-refl

∙-congRight : (x y z : Carrier) -> y ≈ z -> (x ∙ y) ≈ (x ∙ z)
∙-congRight x y z p = ∙-cong ≈-refl p

-- required by proof of lemma5
lemma0 : (x y z : Carrier) -> (x ≈ z) -> (y ≈ z) -> (x ≈ y)
lemma0 x y z p q = ≈-trans p (≈-sym q)

-- required by proof of lemma4
lemma1 : (x y : Carrier) -> (x ≈ y) -> square x ≈ square y
lemma1 x y p = ∙-cong p p

-- required by proof of lemma3
lemma2 : (x y z : Carrier) -> (x ∙ (y ∙ z)) ≈ (y ∙ (x ∙ z))
lemma2 x y z = begin
  (x ∙ (y ∙ z)) ≈⟨ comm x (y ∙ z) ⟩ 
  (y ∙ z) ∙ x   ≈⟨ assoc y z x ⟩ 
  y ∙ (z ∙ x)   
    ≈⟨ ∙-congRight y (z ∙ x) (x ∙ z) (comm z x)  ⟩ 
  (y ∙ (x ∙ z))
  ∎

-- required by proof of lemma4
lemma3 : (x y z : Carrier) -> 
         (x ∙ (x ∙ (square y))) ≈ square (x ∙ y)
lemma3 x y z = begin
   (x ∙ (x ∙ (square y))) 
     ≈⟨ ∙-congRight x (x ∙ (y ∙ y)) (y ∙ (x ∙ y)) (lemma2 x y y) ⟩
   (x ∙ (y ∙ (x ∙ y))) ≈⟨ assoc' x y (x ∙ y) ⟩
   square (x ∙ y)
   ∎

-- required by proof of lemma6
lemma4 : (x y z : Carrier) -> ((x ∙ z) ≈ y) ->
         (x ∙ (x ∙ square z)) ≈ square y
lemma4 x y z p = begin
  x ∙ (x ∙ square z) ≈⟨ lemma3 x z z ⟩
  square (x ∙ z) ≈⟨ lemma1 (x ∙ z) y p ⟩
  square y
  ∎

-- required by proof of lemma6
lemma5 : (w x y z : Carrier) -> ((w ∙ x) ≈ z) ->
         ((w ∙ y) ≈ z) -> (x ≈ y)
lemma5 w x y z p q 
  = cancel x y w (lemma0 (w ∙ x) (w ∙ y) z p q)

-- required by proof of lemma8
lemma6 : (w x y z : Carrier) -> 
         ((w ∙ (square x)) ≈ square y) -> (w ∙ z) ≈ y ->
         (w ∙ (square z)) ≈ square x
lemma6 w x y z s t 
  = lemma5 w (w ∙ square z) (square x) (square y) 
           (lemma4 w y z t) s

-- required by proof of lemma8
lemma7 : (p x : Carrier) -> p isPrime ->
         p divides (square x) -> p divides x
lemma7 p x s t = ⊎-elim (λ y → y) (λ y → y) (s x x t)
-- can we prove above without ⊎-elim?

-- required by proof of lemma9
lemma8 : (p x y : Carrier) -> p isPrime ->
         (((p ∙ square x)) ≈ square y) ->
         ∃ (λ z -> ((p ∙ z) ≈ y) × ((p ∙ square z) ≈ square x))
lemma8 p x y s t 
  = ∃-elim rem 
            (λ w u → w , (u , (lemma6 p x y w t u)))
      where rem : p divides y
            rem = lemma7 p y s ((square x) , t)
-- can we prove above without ∃-elim?

-- needed for the theorem
lemma9 : (p : Carrier) -> (h2 : p isPrime) -> (x : Carrier) ->
         (h3 : Square p x) -> 
         ∃ (λ (x1 : Carrier) -> ((p ∙ x1 ≈ x) × Square p x1))
lemma9 p h2 x h3 
  = ∃-elim h3 (λ y h4 → 
                ∃-elim (lemma8 p x y h2 h4) 
                        (λ y1 h5 → 
                           let 
                             rem2 : p ∙ square y1 ≈ square x
                             rem2 = ×-elimRight 
                                      (multiple p y1 y) 
                                      (multiple p (square y1) 
                                                  (square x)) 
                                      h5
                           in 
                           ∃-elim (lemma8 p y1 x h2 rem2) 
                                   (λ x1 h6 → 
                                      let rem3 : p ∙ x1 ≈ x
                                          rem3 = ×-elimLeft 
                                                   (multiple p x1 x) 
                                                   (multiple p 
                                                      (square x1) 
                                                      (square y1))
                                                   h6
                                          rem4 : p ∙ square x1 ≈ square y1
                                          rem4 = ×-elimRight 
                                                   (multiple p x1 x) 
                                                   (multiple p 
                                                      (square x1) 
                                                      (square y1)) 
                                                   h6
                                      in
                                      x1 , (rem3 , (y1 , rem4)))))
-- TODO: rewrite above more simple
