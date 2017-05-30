module NatPlus where

open import Algebra.FunctionProperties
open import Algebra.Structures

open import Data.Nat as ℕ
  using (ℕ; zero; suc; pred; _+_; _*_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties.Simple
  using (+-suc; +-assoc; *-comm; distribʳ-*-+; +-right-identity; *-assoc)
open import Data.Nat.Properties
  using (≤-steps)
open import Data.Product as Prod
open import Data.Empty
open import Data.Unit

import Level

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P

open import Function
  using (_∘_; _$_; id; flip)
import Function.Related as Related

Pos : ℕ → Set
Pos zero = ⊥
Pos (suc n) = ⊤

data ℕ⁺ : Set where
  n⁺ : (x : ℕ) (p : Pos x) → ℕ⁺

fromℕ⁺ : ℕ⁺ → ℕ
fromℕ⁺ (n⁺ x p) = x

pred⁺ : ℕ⁺ → ℕ
pred⁺ (n⁺ zero ())
pred⁺ (n⁺ (suc x) p) = x

1⁺ : ℕ⁺
1⁺ = n⁺ 1 tt

2⁺ : ℕ⁺
2⁺ = n⁺ 2 tt

infix 4 _≈⁺_

_≈⁺_ : (m n : ℕ⁺) → Set
n⁺ x p ≈⁺ n⁺ y q = x ≡ y

irrel-pos : ∀ {x : ℕ} → (p q : Pos x) → p ≡ q
irrel-pos {zero} () ()
irrel-pos {suc x} tt tt = refl

≈⁺⇒≡ : ∀ {m n} → m ≈⁺ n → m ≡ n
≈⁺⇒≡ {n⁺ x p} {n⁺ .x q} refl
  rewrite irrel-pos p q
  = refl

≡⇒≈⁺ : ∀ {m n} → m ≡ n → m ≈⁺ n
≡⇒≈⁺ {n⁺ x p} refl = refl

pos+ : ∀ x → Pos x → ∀ y → Pos (x + y)
pos+ zero () y
pos+ (suc x) tt y = tt

pos* : ∀ x → Pos x → ∀ y → Pos y → Pos (x * y)
pos* zero () y q
pos* (suc x) tt zero ()
pos* (suc x) tt (suc y) tt = tt

infixl 6 _⊕_
infixl 7 _⊛_

_⊕_ : (m n : ℕ⁺) → ℕ⁺
n⁺ x p ⊕ n⁺ y q = n⁺ (x + y) (pos+ x p y)

_⊛_ : (m n : ℕ⁺) → ℕ⁺
n⁺ x p ⊛ n⁺ y q = n⁺ (x * y) (pos* x p y q)

⊛-assoc : Associative _≡_ _⊛_
⊛-assoc (n⁺ x p) (n⁺ y q) (n⁺ z r) =
  ≈⁺⇒≡ $ *-assoc x y z

⊛-leftIdentity : ∀ n → 1⁺ ⊛ n ≡ n
⊛-leftIdentity (n⁺ x p) =
  ≈⁺⇒≡ $ +-right-identity x

⊛-comm : ∀ m n → m ⊛ n ≡  n ⊛ m
⊛-comm (n⁺ x p) (n⁺ y q) =
  ≈⁺⇒≡ $ *-comm x y


⊛-isCommutativeMonoid : IsCommutativeMonoid {Level.zero} _≡_ _⊛_ 1⁺
⊛-isCommutativeMonoid = record 
  { isSemigroup = record
      { isEquivalence = isEquivalence
      ; assoc         = ⊛-assoc
      ; ∙-cong        = cong₂ _⊛_
      }
  ; identityˡ = ⊛-leftIdentity
  ; comm      = ⊛-comm
  }

cancel-+-left : ∀ x y z → z + x ≡ z + y → x ≡ y
cancel-+-left x y zero x≡y = x≡y
cancel-+-left x y (suc z) =
  suc z + x ≡ suc z + y
    ≡⟨ refl ⟩
  suc (z + x) ≡ suc (z + y)
    ∼⟨ cong pred ⟩
  z + x ≡ z + y
    ∼⟨ cancel-+-left x y z ⟩
  x ≡ y
  ∎
  where open Related.EquationalReasoning

cancel-*-right : ∀ x y z → x * suc z ≡ y * suc z → x ≡ y
cancel-*-right zero zero z 0≡0 = 0≡0
cancel-*-right zero (suc y) z ()
cancel-*-right (suc x) zero z ()
cancel-*-right (suc x) (suc y) z =
  suc x * suc z ≡ suc y * suc z
    ≡⟨ refl ⟩
  suc (z + x * suc z) ≡ suc (z + y * suc z)
    ∼⟨ cong pred ⟩
  z + x * suc z ≡ z + y * suc z
    ∼⟨ cancel-+-left (x * suc z) (y * suc z) z ⟩
  x * suc z ≡ y * suc z
    ∼⟨ cancel-*-right x y z ⟩
  x ≡ y
    ∼⟨ cong suc ⟩
  suc x ≡ suc y
  ∎
  where open Related.EquationalReasoning

cancel-*-left : ∀ x y z → suc z * x ≡ suc z * y → x ≡ y
cancel-*-left x y z =
  suc z * x ≡ suc z * y
    ≡⟨ cong₂ _≡_ (*-comm (suc z) x) (*-comm (suc z) y) ⟩
  x * suc z ≡ y * suc z
    ∼⟨ cancel-*-right x y z ⟩
  x ≡ y
  ∎
  where open Related.EquationalReasoning

cancel-⊛-left : ∀ m n k → k ⊛ m ≡ k ⊛ n → m ≡ n
cancel-⊛-left (n⁺ x p) (n⁺ y q) (n⁺ zero ()) h
cancel-⊛-left (n⁺ x p) (n⁺ y q) (n⁺ (suc z′) tt) h
  with ≡⇒≈⁺ h
... | sz′*x≡sz′*y with cancel-*-left x y z′ sz′*x≡sz′*y
... | x≡y rewrite x≡y
  = cong (n⁺ y) (irrel-pos p q)
