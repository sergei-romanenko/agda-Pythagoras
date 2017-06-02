module Corollary where

open import Agda.Primitive

open import Algebra
open import Function
  using (_∘_; _$_)
import Function.Related as Related

import Algebra.FunctionProperties as FunctionProperties
open FunctionProperties
open import Algebra.Structures
open import Agda.Primitive
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _<′_; ≤′-refl; ≤′-step; _≤′_)
open import Data.Nat.Properties
  using (s≤′s)
open import Data.Product
  using (Σ; _×_; _,_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Empty
open import Data.Unit

open import Induction.WellFounded
  using (Acc; acc; module Subrelation; module Inverse-image)
open import Induction.Nat
  using (<-well-founded)

open import NatPlus
open import 2Divides

import Cancel
open Cancel {_} {_} {ℕ⁺} (_≡_)
open import CancellativeAbelianMonoid

isCancellativeAbelianMonoid : 
  IsCancellativeAbelianMonoid _≡_ _⊛_ 1⁺
isCancellativeAbelianMonoid
  = record {
      isCommutativeMonoid = ⊛-isCommutativeMonoid
    ; cancel = cancel-⊛-left
    }

m : CancellativeAbelianMonoid lzero lzero
m = record {
      Carrier = ℕ⁺
    ; _≈_ = _≡_
    ; _∙_ = _⊛_
    ; ε   = 1⁺
    ; isCancellativeAbelianMonoid = isCancellativeAbelianMonoid
    }

open import Noether
open import Property lzero lzero m
open import Theorem lzero m

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

lemma2′ : (P : ℕ⁺ → Set) →
  ((m : ℕ⁺) → ((k : ℕ⁺) → 2⁺ ⊛ k ≡ m → P k) → P m) →
  (n : ℕ⁺) (a : Acc _<′_ (fromℕ⁺ n)) → P n
lemma2′ P f (x , p) (acc rs) with  2∣? x
... | no ¬∃k→2*k≡x = f (x , p) help
  where help : (k : ℕ⁺) → 2⁺ ⊛ k ≡ (x , p) → P k
        help (z , r) 2⊛k≡n = ⊥-elim (¬∃k→2*k≡x (z , cong fromℕ⁺ 2⊛k≡n))
... | yes (k , 2*k≡x) =
  f (x , p) (λ {(l , s) ≡n → lemma2′ P f (l , s)
    (rs l (subst (_<′_ l) (cong fromℕ⁺ ≡n) (<′2* l s)))})

lemma2 : Noether Carrier (multiple 2⁺)
lemma2 P f n = lemma2′ P f n (<-well-founded (fromℕ⁺ n))

corollary : NotSquare 2⁺
corollary = theorem 2⁺ prime-2⁺ lemma2

_<′⁺_ : (m n : ℕ⁺) → Set
m <′⁺ n = fromℕ⁺ m <′ fromℕ⁺ n

2⁺*≡⇒<′⁺ : ∀ {m n} → 2⁺ ⊛ m ≡ n → m <′⁺ n
2⁺*≡⇒<′⁺ {x , p} {y , q} 2m≡n
  rewrite sym $ (cong fromℕ⁺ 2m≡n)
  = <′2* x p

module Wf-<′⁺ = Inverse-image {A = ℕ⁺} {B = ℕ} {_<′_} fromℕ⁺
module Wf-2⁺*≡ = Subrelation {A = ℕ⁺} {multiple 2⁺} {_<′⁺_} 2⁺*≡⇒<′⁺

lemma2₂ : ∀ (k m : ℕ⁺) → 2⁺ ∙ (k ⊛ k) ≡ (m ⊛ m) →
             Acc (multiple 2⁺) m → ⊥
lemma2₂ k m 2kk≡mm acc-m =
  theorem₂ 2⁺ prime-2⁺ k m 2kk≡mm acc-m

corollary₂ : NotSquare 2⁺
corollary₂ k m 2kk≡mm =
  lemma2₂ k m 2kk≡mm
          (Wf-2⁺*≡.well-founded (Wf-<′⁺.well-founded <-well-founded) m)
