module NatStarProperties where

open import Function
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Empty
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
  as PropEq
open PropEq.≡-Reasoning

open import NatStar

-- copy properties from the Agda standard library
-- Data.Nat.Properties

+-assoc : Associative _≡_ _+_
+-assoc one _ _ = refl
+-assoc (succ m) n o = begin
  succ m + n + o ≡⟨ cong succ (+-assoc m n o) ⟩
  succ m + (n + o)
  ∎

m+1≡1+m : ∀ m → m + one ≡ succ m
m+1≡1+m one = refl
m+1≡1+m (succ m) = cong succ (m+1≡1+m m)

m+1+n≡1+m+n : ∀ m n → m + succ n ≡ succ (m + n)
m+1+n≡1+m+n one n = refl
m+1+n≡1+m+n (succ m) n = cong succ (m+1+n≡1+m+n m n)

+-comm : Commutative _≡_ _+_
+-comm one one = refl
+-comm one (succ n) = cong succ (sym $ m+1≡1+m n)
+-comm (succ m) n =
 begin
  succ (m + n)
    ≡⟨ cong succ (+-comm m n) ⟩
  succ (n + m)
    ≡⟨ sym $ m+1+n≡1+m+n n m ⟩
  n + succ m
  ∎

*-distrib-right-+ :  ∀ x y z → ((y + z) * x) ≡ ((y * x) + (z * x))
*-distrib-right-+ m one o = refl
*-distrib-right-+ m (succ n) o = begin
  (succ n + o) * m    ≡⟨ refl ⟩
  m + (n + o) * m     ≡⟨ cong (_+_ m) $ *-distrib-right-+ m n o ⟩
  m + (n * m + o * m) ≡⟨ sym $ +-assoc m (n * m) (o * m) ⟩
  m + n * m + o * m   ≡⟨ refl ⟩
  succ n * m + o * m
  ∎

*-assoc : Associative _≡_ _*_
*-assoc one n o = refl
*-assoc (succ m) n o = begin
  (succ m * n) * o    ≡⟨ refl ⟩
  (n + m * n) * o     ≡⟨ *-distrib-right-+ o n (m * n) ⟩
  n * o + (m * n) * o ≡⟨ cong (λ x → n * o + x) $ *-assoc m n o ⟩
  n * o + m * (n * o) ≡⟨ refl ⟩
  succ m * (n * o)
  ∎

*-one : ∀ n -> n * one ≡ n
*-one one = refl
*-one (succ m) = cong succ (*-one m)

m*1+n≡m+mn : ∀ m n → m * succ n ≡ m + m * n
m*1+n≡m+mn one n = refl
m*1+n≡m+mn (succ m) n = begin
  succ (n + m * succ n)  ≡⟨ refl ⟩
  succ n + m * succ n    ≡⟨ cong (λ x → succ n + x) (m*1+n≡m+mn m n) ⟩
  succ n + (m + m * n)   ≡⟨ refl ⟩
  succ (n + (m + m * n)) ≡⟨ cong succ (sym $ +-assoc n m (m * n)) ⟩
  succ (n + m + m * n)   ≡⟨ cong (λ x → succ (x + m * n)) (+-comm n m) ⟩
  succ (m + n + m * n)   ≡⟨ cong succ (+-assoc m n (m * n)) ⟩
  succ (m + (n + m * n)) ≡⟨ refl ⟩
  succ (m + (n + m * n))
  ∎

*-comm  : Commutative _≡_ _*_
*-comm one n = sym (*-one n)
*-comm (succ m) n = begin
  n + m * n ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩
  n + n * m ≡⟨ sym (m*1+n≡m+mn n m) ⟩
  n * succ m
  ∎

*-leftIdentity : LeftIdentity _≡_ one _*_
*-leftIdentity x = refl

*-isCommutativeMonoid : IsCommutativeMonoid _≡_ _*_ one
*-isCommutativeMonoid = record 
  { isSemigroup = record
      { isEquivalence = PropEq.isEquivalence
      ; assoc         = *-assoc
      ; ∙-cong        = cong₂ _*_
      }
  ; identityˡ = *-leftIdentity
  ; comm      = *-comm
  }

pred : NatStar -> NatStar
pred one = one
pred (succ m) = m

≡-succ-elim : ∀ x y -> succ x ≡ succ y -> x ≡ y
≡-succ-elim x y p = cong pred p

cancel-+-left : ∀ x y z -> z + x ≡ z + y -> x ≡ y
cancel-+-left x y one p = ≡-succ-elim x y p
cancel-+-left x y (succ z) p 
  = cancel-+-left x y z (cong pred p)

cancel-+-right : ∀ x y z -> x + z ≡ y + z -> x ≡ y
cancel-+-right x y z p 
  = cancel-+-left x y z q
      where q : z + x ≡ z + y
            q = begin
              z + x ≡⟨ +-comm z x ⟩
              x + z ≡⟨ p ⟩
              y + z ≡⟨ +-comm y z ⟩
              z + y
              ∎

+-⊥-right : ∀ x y -> x ≡ x + y -> ⊥
+-⊥-right one y ()
+-⊥-right (succ x) y p 
  = +-⊥-right x y (≡-succ-elim x (x + y) p)

+-⊥-left : ∀ x y -> x + y ≡ x -> ⊥
+-⊥-left one y ()
+-⊥-left (succ x) y p 
  = +-⊥-left x y (≡-succ-elim (x + y) x p)

cancel-*-right : ∀ x y z -> x * z ≡ y * z -> x ≡ y
cancel-*-right one one z p = refl
cancel-*-right one (succ y) one p with begin
  one ≡⟨ p ⟩
  succ (y * one) ≡⟨ cong succ (*-comm y one) ⟩
  succ (one * y) ≡⟨ cong succ refl ⟩
  succ y
  ∎
... | ()
cancel-*-right one (succ y) (succ z) p 
  with +-⊥-right (succ (succ z)) (y * succ z) (cong succ p)
... | ()
cancel-*-right (succ x) one z p 
  with +-⊥-left (succ z) (x * z) (cong succ p)
... | ()
cancel-*-right (succ x) (succ y) z p 
  = cong succ (cancel-*-right x y z 
      (cancel-+-left (x * z) (y * z) z p))

cancel-*-left : ∀ x y z -> z * x ≡ z * y -> x ≡ y
cancel-*-left x y z p 
  = cancel-*-right x y z (lemma x y z p)
  where lemma : ∀ x y z -> z * x ≡ z * y -> x * z ≡ y * z
        lemma x y z p = begin
          x * z ≡⟨ *-comm x z ⟩
          z * x ≡⟨ p ⟩
          z * y ≡⟨ *-comm z y ⟩
          y * z
          ∎
