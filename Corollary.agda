module Corollary where

open import Agda.Primitive

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _<′_; ≤′-refl; ≤′-step; _≤′_)
open import Data.Nat.Properties
  using (s≤′s)
open import Data.Product
  using (Σ; _×_; _,_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
  using (⊥)

open import Function
  using (_∘_; _$_)
import Function.Related as Related

open import Induction.WellFounded
  using (Acc; acc; WellFounded; module Subrelation; module InverseImage)
open import Data.Nat.Induction
  using (<′-wellFounded)

open import NatPlus
open import 2Divides

open import Cancellative

isCancellativeAbelianMonoid : 
  IsCancellativeAbelianMonoid _≡_ _⊛_ 1⁺
isCancellativeAbelianMonoid = record
  { isCommutativeMonoid = ⊛-isCommutativeMonoid
  ; cancel = cancel-⊛-left
  }

mnd : CancellativeAbelianMonoid lzero lzero
mnd = record
  { Carrier = ℕ⁺
  ; _≈_ = _≡_
  ; _∙_ = _⊛_
  ; ε   = 1⁺
  ; isCancellativeAbelianMonoid = isCancellativeAbelianMonoid
  }

open import Theorem lzero mnd


--Prime 2⁺

divides⇒∣ : (n : ℕ⁺) → 2⁺ divides n → 2∣ fromℕ⁺ n
divides⇒∣ (x , p) ((y , q) , h) =
  y , cong fromℕ⁺ h

∣⇒divides : (n : ℕ⁺) → 2∣ fromℕ⁺ n → 2⁺ divides n
∣⇒divides (.0 , ()) (0 , refl)
∣⇒divides (.(suc (y + suc (y + 0))) , tt) (suc y , refl) =
  (suc y , tt) , ≈⁺⇒≡ refl

prime-2⁺ : Prime 2⁺
prime-2⁺ (x , p) (y , q) h
  with divides⇒∣ ((x , p) ⊛ (y , q)) h
... | 2∣x*y with 2∣*⊎ {x} {y} 2∣x*y
... | inj₁ 2∣x = inj₁ (∣⇒divides (x , p) 2∣x)
... | inj₂ 2∣y = inj₂ (∣⇒divides (y , q) 2∣y)


-- WellFounded (multiple 2⁺)

<′2* : ∀ x → Pos x → x <′ 2 * x
<′2* zero ()
<′2* (suc zero) tt = ≤′-refl
<′2* (suc (suc x)) tt = step (<′2* (suc x) tt)
  where
  open Related.EquationalReasoning hiding (sym)
  step : 1 + x <′ 2 * (1 + x) → 2 + x <′ 2 * (2 + x)
  step =
    1 + x <′ 2 * (1 + x)
      ∼⟨ ≤′-step ⟩
    1 + x <′ 1 + 2 * (1 + x)
      ∼⟨ s≤′s ⟩
    2 + x <′ 2 + 2 * (1 + x)
      ≡⟨ cong (_<′_ (2 + x))  (sym $ 2*-suc (1 + x)) ⟩
    2 + x <′ 2 * (2 + x)
    ∎

_<′⁺_ : (m n : ℕ⁺) → Set
m <′⁺ n = fromℕ⁺ m <′ fromℕ⁺ n

2⁺*≡⇒<′⁺ : ∀ {m n} → 2⁺ ⊛ m ≡ n → m <′⁺ n
2⁺*≡⇒<′⁺ {x , p} {y , q} 2m≡n
  rewrite sym $ (cong fromℕ⁺ 2m≡n)
  = <′2* x p

module Wf-<′⁺ = InverseImage {_<_ = _<′_} fromℕ⁺
module Wf-2⁺*≡ = Subrelation {_<₁_ = multiple 2⁺} {_<₂_ = _<′⁺_} 2⁺*≡⇒<′⁺

2⁺⊛-well-founded : WellFounded (multiple 2⁺)
2⁺⊛-well-founded =
  Wf-2⁺*≡.wellFounded $ Wf-<′⁺.wellFounded $ <′-wellFounded

--
-- 2⁺ is not rational.
--

corollary : NotSquare 2⁺
corollary =
  theorem 2⁺ prime-2⁺ 2⁺⊛-well-founded
