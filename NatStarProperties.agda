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
+-assoc (suc m) n o = begin
  suc m + n + o ≡⟨ cong suc (+-assoc m n o) ⟩
  suc m + (n + o)
  ∎

m+1≡1+m : ∀ m → m + one ≡ suc m
m+1≡1+m one = refl
m+1≡1+m (suc m) = cong suc (m+1≡1+m m)

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc (m + n)
m+1+n≡1+m+n one n = refl
m+1+n≡1+m+n (suc m) n = cong suc (m+1+n≡1+m+n m n)

+-comm : Commutative _≡_ _+_
+-comm one one = refl
+-comm one (suc n) = cong suc (sym $ m+1≡1+m n)
+-comm (suc m) n =
 begin
  suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩
  suc (n + m)
    ≡⟨ sym $ m+1+n≡1+m+n n m ⟩
  n + suc m
  ∎

*-distrib-right-+ :  ∀ x y z → ((y + z) * x) ≡ ((y * x) + (z * x))
*-distrib-right-+ m one o = refl
*-distrib-right-+ m (suc n) o = begin
  (suc n + o) * m    ≡⟨ refl ⟩
  m + (n + o) * m     ≡⟨ cong (_+_ m) $ *-distrib-right-+ m n o ⟩
  m + (n * m + o * m) ≡⟨ sym $ +-assoc m (n * m) (o * m) ⟩
  m + n * m + o * m   ≡⟨ refl ⟩
  suc n * m + o * m
  ∎

*-assoc : Associative _≡_ _*_
*-assoc one n o = refl
*-assoc (suc m) n o = begin
  (suc m * n) * o    ≡⟨ refl ⟩
  (n + m * n) * o     ≡⟨ *-distrib-right-+ o n (m * n) ⟩
  n * o + (m * n) * o ≡⟨ cong (λ x → n * o + x) $ *-assoc m n o ⟩
  n * o + m * (n * o) ≡⟨ refl ⟩
  suc m * (n * o)
  ∎

*-one : ∀ n → n * one ≡ n
*-one one = refl
*-one (suc m) = cong suc (*-one m)

m*1+n≡m+mn : ∀ m n → m * suc n ≡ m + m * n
m*1+n≡m+mn one n = refl
m*1+n≡m+mn (suc m) n = begin
  suc (n + m * suc n)  ≡⟨ refl ⟩
  suc n + m * suc n    ≡⟨ cong (λ x → suc n + x) (m*1+n≡m+mn m n) ⟩
  suc n + (m + m * n)   ≡⟨ refl ⟩
  suc (n + (m + m * n)) ≡⟨ cong suc (sym $ +-assoc n m (m * n)) ⟩
  suc (n + m + m * n)   ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
  suc (m + n + m * n)   ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
  suc (m + (n + m * n)) ≡⟨ refl ⟩
  suc (m + (n + m * n))
  ∎

*-comm  : Commutative _≡_ _*_
*-comm one n = sym (*-one n)
*-comm (suc m) n = begin
  n + m * n ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩
  n + n * m ≡⟨ sym (m*1+n≡m+mn n m) ⟩
  n * suc m
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

pred : NatStar → NatStar
pred one = one
pred (suc m) = m

≡-suc-elim : ∀ x y → suc x ≡ suc y → x ≡ y
≡-suc-elim x y p = cong pred p

cancel-+-left : ∀ x y z → z + x ≡ z + y → x ≡ y
cancel-+-left x y one p = ≡-suc-elim x y p
cancel-+-left x y (suc z) p 
  = cancel-+-left x y z (cong pred p)

cancel-+-right : ∀ x y z → x + z ≡ y + z → x ≡ y
cancel-+-right x y z p 
  = cancel-+-left x y z q
      where q : z + x ≡ z + y
            q = begin
              z + x ≡⟨ +-comm z x ⟩
              x + z ≡⟨ p ⟩
              y + z ≡⟨ +-comm y z ⟩
              z + y
              ∎

+-⊥-right : ∀ x y → x ≡ x + y → ⊥
+-⊥-right one y ()
+-⊥-right (suc x) y p 
  = +-⊥-right x y (≡-suc-elim x (x + y) p)

+-⊥-left : ∀ x y → x + y ≡ x → ⊥
+-⊥-left one y ()
+-⊥-left (suc x) y p 
  = +-⊥-left x y (≡-suc-elim (x + y) x p)

cancel-*-right : ∀ x y z → x * z ≡ y * z → x ≡ y
cancel-*-right one one z p = refl
cancel-*-right one (suc y) one p with begin
  one ≡⟨ p ⟩
  suc (y * one) ≡⟨ cong suc (*-comm y one) ⟩
  suc (one * y) ≡⟨ cong suc refl ⟩
  suc y
  ∎
... | ()
cancel-*-right one (suc y) (suc z) p 
  with +-⊥-right (suc (suc z)) (y * suc z) (cong suc p)
... | ()
cancel-*-right (suc x) one z p 
  with +-⊥-left (suc z) (x * z) (cong suc p)
... | ()
cancel-*-right (suc x) (suc y) z p 
  = cong suc (cancel-*-right x y z 
      (cancel-+-left (x * z) (y * z) z p))

cancel-*-left : ∀ x y z → z * x ≡ z * y → x ≡ y
cancel-*-left x y z p 
  = cancel-*-right x y z (lemma x y z p)
  where lemma : ∀ x y z → z * x ≡ z * y → x * z ≡ y * z
        lemma x y z p = begin
          x * z ≡⟨ *-comm x z ⟩
          z * x ≡⟨ p ⟩
          z * y ≡⟨ *-comm z y ⟩
          y * z
          ∎
