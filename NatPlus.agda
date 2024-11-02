module NatPlus where

open import Algebra
  using (Identity; Associative; Magma; IsMagma; IsMonoid; IsCommutativeMonoid)
open import Algebra.Structures.Biased

open import Data.Nat as ℕ
  using (ℕ; zero; suc; pred; _+_; _*_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (+-assoc; *-comm; +-identityʳ; +-identityˡ; *-identityʳ; *-identityˡ; *-assoc)
open import Data.Nat.Properties
  using (≤-stepsˡ)
open import Data.Empty
  using (⊥)
open import Data.Unit
  using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import Relation.Binary.Structures
  using (IsEquivalence)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; isEquivalence)

open import Function
  using(_$_)
import Function.Related as Related

Pos : ℕ → Set
Pos zero = ⊥
Pos (suc n) = ⊤

infixr 4 _,_

data ℕ⁺ : Set where
  _,_ : (x : ℕ) (p : Pos x) → ℕ⁺

fromℕ⁺ : ℕ⁺ → ℕ
fromℕ⁺ (x , p) = x

pred⁺ : ℕ⁺ → ℕ
pred⁺ (zero , ())
pred⁺ (suc x , p) = x

1⁺ : ℕ⁺
1⁺ = 1 , tt

2⁺ : ℕ⁺
2⁺ = 2 , tt

infix 4 _≈⁺_

_≈⁺_ : (m n : ℕ⁺) → Set
(x , p) ≈⁺ (y , q) = x ≡ y

irrel-pos : ∀ {x : ℕ} → (p q : Pos x) → p ≡ q
irrel-pos {zero} () ()
irrel-pos {suc x} tt tt = refl

≈⁺⇒≡ : ∀ {m n} → m ≈⁺ n → m ≡ n
≈⁺⇒≡ {x , p} {.x , q} refl
  rewrite irrel-pos p q
  = refl

≡⇒≈⁺ : ∀ {m n} → m ≡ n → m ≈⁺ n
≡⇒≈⁺ {x , p} refl = refl

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
(x , p) ⊕ (y , q) = x + y , pos+ x p y

_⊛_ : (m n : ℕ⁺) → ℕ⁺
(x , p) ⊛ (y , q) = x * y , pos* x p y q

⊛-assoc : Associative _≡_ _⊛_
⊛-assoc (x , p) (y , q) (z , r) =
  ≈⁺⇒≡ $ *-assoc x y z

⊛-identityˡ : ∀ n → 1⁺ ⊛ n ≡ n
⊛-identityˡ (x , p) =
  ≈⁺⇒≡ $ +-identityʳ x

⊛-identityʳ : ∀ n → n ⊛ 1⁺ ≡ n
⊛-identityʳ (x , p) =
  ≈⁺⇒≡ $ *-identityʳ x

⊛-identity : Identity _≡_ 1⁺ _⊛_
⊛-identity = (⊛-identityˡ , ⊛-identityʳ)

⊛-comm : ∀ m n → m ⊛ n ≡  n ⊛ m
⊛-comm (x , p) (y , q) =
  ≈⁺⇒≡ $ *-comm x y

⊛-isCommutativeMonoid : IsCommutativeMonoid _≡_ _⊛_ 1⁺
⊛-isCommutativeMonoid = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence
        ; ∙-cong = cong₂ _⊛_
        }
      ; assoc = ⊛-assoc
    }
    ; identity = ⊛-identity
    }
  ; comm = ⊛-comm
  }

+-cancelˡ-≡ : ∀ x y z → z + x ≡ z + y → x ≡ y
+-cancelˡ-≡ x y zero x≡y =
  x≡y
+-cancelˡ-≡ x y (suc z) =
  suc z + x ≡ suc z + y
    ≡⟨ refl ⟩
  suc (z + x) ≡ suc (z + y)
    ∼⟨ cong pred ⟩
  z + x ≡ z + y
    ∼⟨ +-cancelˡ-≡ x y z ⟩
  x ≡ y
  ∎
  where open Related.EquationalReasoning

*-cancelʳ-≡ : ∀ x y z → x * suc z ≡ y * suc z → x ≡ y
*-cancelʳ-≡ zero zero z 0≡0 = 0≡0
*-cancelʳ-≡ zero (suc y) z ()
*-cancelʳ-≡ (suc x) zero z ()
*-cancelʳ-≡ (suc x) (suc y) z =
  suc x * suc z ≡ suc y * suc z
    ≡⟨ refl ⟩
  suc (z + x * suc z) ≡ suc (z + y * suc z)
    ∼⟨ cong pred ⟩
  z + x * suc z ≡ z + y * suc z
    ∼⟨ +-cancelˡ-≡ (x * suc z) (y * suc z) z ⟩
  x * suc z ≡ y * suc z
    ∼⟨ *-cancelʳ-≡ x y z ⟩
  x ≡ y
    ∼⟨ cong suc ⟩
  suc x ≡ suc y
  ∎
  where open Related.EquationalReasoning

*-cancelˡ-≡ : ∀ x y z → suc z * x ≡ suc z * y → x ≡ y
*-cancelˡ-≡ x y z =
  suc z * x ≡ suc z * y
    ≡⟨ cong₂ _≡_ (*-comm (suc z) x) (*-comm (suc z) y) ⟩
  x * suc z ≡ y * suc z
    ∼⟨ *-cancelʳ-≡ x y z ⟩
  x ≡ y
  ∎
  where open Related.EquationalReasoning

⊛-cancelˡ-≡ : ∀ m n k → k ⊛ m ≡ k ⊛ n → m ≡ n
⊛-cancelˡ-≡ (x , p) (y , q) (zero , ()) h
⊛-cancelˡ-≡ (x , p) (y , q) (suc z′ , tt) h
  with ≡⇒≈⁺ h
... | sz′*x≡sz′*y with *-cancelˡ-≡ x y z′ sz′*x≡sz′*y
... | x≡y rewrite x≡y
  = cong (_,_ y) (irrel-pos p q)
