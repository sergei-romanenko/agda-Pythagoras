module Corollary where

open import Agda.Primitive

open import Algebra
open import Function
import Function.Related as Related

import Algebra.FunctionProperties as FunctionProperties
open FunctionProperties
open import Algebra.Structures
open import Agda.Primitive
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality as P

open import Data.Nat as ℕ
open import Data.Nat.Properties.Simple
  using (+-suc; +-assoc; *-comm; distribʳ-*-+; +-right-identity; *-assoc)
open import Data.Nat.Properties
  using (s≤′s)
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Empty
open import Data.Unit

open import Induction.WellFounded
open import Induction.Nat

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
import Property
open Property lzero lzero m
import Theorem 
open Theorem lzero m

pos-2* : ∀ x → Pos (2 * x) → Pos x
pos-2* zero ()
pos-2* (suc x) tt = tt

divides⇒∣ : (x : ℕ) (p : Pos x) → 2⁺ divides (x ,  p) → 2∣ x
divides⇒∣ x p ((y , q) , h) =
  y , cong fromℕ⁺ h

∣⇒divides : (x : ℕ) (p : Pos x) → 2∣ x → 2⁺ divides (x , p)
∣⇒divides x p (z , 2*z≡x)
  rewrite sym 2*z≡x
  = (z , pos-2* z p) , ≈⁺⇒≡ refl

lemma1 : 2⁺ isPrime
lemma1 (x , p) (y , q) h
  with divides⇒∣ (x * y) (pos* x p y q) h
... | 2∣x*y with 2∣*⊎ {x} {y} 2∣x*y
... | inj₁ 2∣x = inj₁ (∣⇒divides x p 2∣x)
... | inj₂ 2∣y = inj₂ (∣⇒divides y q 2∣y)

2*suc≢0 : ∀ x → x + suc (x + 0) ≡ 0 → ⊥
2*suc≢0 x h =
  0≢suc (sym $ subst (λ z → z ≡ 0) (+-suc x (x + zero)) h)

<′2* : ∀ k → Pos k → k <′ 2 * k
<′2* zero ()
<′2* (suc zero) tt = ≤′-refl
<′2* (suc (suc k)) tt
  rewrite +-suc k (suc (k + 0))
  = s≤′s (≤′-step (<′2* (suc k) tt))

prop′ : (P : ℕ → Set) →
  ((m : ℕ) (q : Pos m) → ((k : ℕ) (r : Pos k) → 2 * k ≡ m → P k) → P m) →
  (n : ℕ) (p : Pos n) (a : Acc _<′_ n)  → P n
prop′ P f n p (acc rs) with 2∣? n
... | no ¬∃k→2*k≡n = f n p help
  where help : (k : ℕ) (r : Pos k) → 2 * k ≡ n → P k
        help k r 2*k≡n = ⊥-elim (¬∃k→2*k≡n (k , 2*k≡n))
... | yes (k , 2*k≡n) =
  f n p (λ l s 2*l≡n → prop′ P f l s (rs l (subst (_<′_ l) 2*l≡n (<′2* l s))))

prop : (P : ℕ → Set) →
  ((m : ℕ) (q : Pos m) → ((k : ℕ) (r : Pos k) → 2 * k ≡ m → P k) → P m) →
  (n : ℕ) (p : Pos n) → P n
prop P f n p = prop′ P f n p (<-well-founded n)

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

corollary : 2⁺ isNotSquare
corollary = theorem 2⁺ lemma1 lemma2
