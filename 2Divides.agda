module 2Divides where

open import Data.Nat
  using (ℕ; zero; suc; pred; _+_; _*_)
open import Data.Nat.Properties
  using (+-suc; +-assoc; +-identityʳ)
open import Data.Product as Prod
  using (_×_; _,_; ∃)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty
  using (⊥)

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; subst; sym; module ≡-Reasoning)

open import Function
  using (_∘_; _$_; _|>_)
import Function.Related as Related

mutual

  data Even : ℕ → Set where
    even0  : Even zero
    even1 : ∀ {n} → Odd n → Even (suc n)

  data Odd : ℕ → Set where
    odd1 : ∀ {n} → Even n → Odd (suc n)

even⊎odd : ∀ n → Even n ⊎ Odd n
even⊎odd zero =
  inj₁ even0
even⊎odd (suc n) =
  [ inj₂ ∘ odd1 , inj₁ ∘ even1 ]′ $ even⊎odd n

2*-suc : ∀ n → 2 * suc n ≡ suc (suc (2 * n))
2*-suc n =
  2 * suc n
    ≡⟨⟩
  suc (n + suc (n + zero))
    ≡⟨ cong suc (+-suc n (n + zero)) ⟩
  suc (suc (n + (n + zero)))
    ≡⟨⟩
  suc (suc (2 * n))
  ∎
  where open ≡-Reasoning

even-2* : ∀ n → Even (2 * n)
even-2* zero =
  even0
even-2* (suc zero) =
  even1 (odd1 even0)
even-2* (suc (suc n)) = even-2* n |>
  Even (2 * n)
    ∼⟨ even1 ∘ odd1 ⟩
  Even (suc (suc (2 *  n)))
    ≡⟨ cong Even (sym $ 2*-suc n) ⟩
  Even (2 * (suc n))
    ∼⟨ even1 ∘ odd1 ⟩
  Even (suc (suc (2 * (suc n))))
    ≡⟨ cong Even (sym $ 2*-suc (suc n)) ⟩
  Even (2 * suc (suc n))
  ∎
  where
  open Related.EquationalReasoning hiding (sym)

even-even+ : ∀ {m n} → Even m → Even (m + n) → Even n
even-even+ even0 even-n =
  even-n
even-even+ (even1 (odd1 {m} even-m)) (even1 (odd1 even+)) =
  even-even+ even-m even+

odd-even* : ∀ {m n} → Odd m → Even (m * n) → Even n
odd-even* (odd1 even0) even-n+0 =
  subst Even (+-identityʳ _) even-n+0
odd-even* {_} {n} (odd1 (even1 {m} odd-m)) =
  Even (n + (n + m * n))
    ≡⟨ cong Even (sym $ +-assoc n n (m * n)) ⟩
  Even ((n + n) + m * n)
    ≡⟨ cong (λ l → Even ((n + l) + m * n)) (sym $ +-identityʳ n) ⟩
  Even (2 * n + m * n)
    ∼⟨ even-even+ (even-2* n) ⟩
  Even (m * n)
    ∼⟨ odd-even* odd-m ⟩
  Even n
  ∎
  where open Related.EquationalReasoning hiding (sym)


infix 4 2∣_

2∣_ : (n : ℕ) → Set
2∣ n = ∃ λ x → 2 * x ≡ n

even⇒2∣ : ∀ {n} → Even n → 2∣ n
even⇒2∣ even0 =
  zero , refl
even⇒2∣ {suc (suc k)} (even1 (odd1 even-k))
  with even⇒2∣ even-k
... | x , 2*x≡k = 1 + x , 2*sx≡ssk
  where
  open ≡-Reasoning
  2*sx≡ssk : 2 * suc x ≡ suc (suc k)
  2*sx≡ssk =
    2 * suc x
      ≡⟨ 2*-suc x  ⟩
    suc (suc (2 * x))
      ≡⟨ cong (suc ∘ suc) 2*x≡k ⟩
    suc (suc k)
    ∎

2∣⇒even : ∀ {n} → 2∣ n → Even n
2∣⇒even {n} (x , 2*x≡n) = even-2* x |>
  Even (2 * x)
    ≡⟨ cong Even 2*x≡n ⟩
  Even n
  ∎
  where open Related.EquationalReasoning hiding (sym)

even*⇒even⊎even : ∀ {m n} → Even (m * n) → Even m ⊎ Even n
even*⇒even⊎even {m} {n} even-m*n
  with even⊎odd m
... | inj₁ even-m = inj₁ even-m
... | inj₂ odd-m = inj₂ (odd-even* odd-m even-m*n)

2∣*⊎ : ∀ {m n} → 2∣ (m * n) → 2∣ m ⊎ 2∣ n
2∣*⊎ {m} {n} =
  2∣ m * n
    ∼⟨ 2∣⇒even ⟩
  Even (m * n)
    ∼⟨ even*⇒even⊎even ⟩
  (Even m ⊎ Even n)
    ∼⟨ Sum.map even⇒2∣ even⇒2∣ ⟩
  (2∣ m ⊎ 2∣ n)
  ∎
  where open Related.EquationalReasoning hiding (sym)
