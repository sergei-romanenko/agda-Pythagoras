module 2Divides where

open import Data.Nat
  using (ℕ; zero; suc; pred; _+_; _*_)
open import Data.Nat.Properties.Simple
  using (+-suc; +-assoc; *-comm; distribʳ-*-+; +-right-identity)
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Empty

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; cong; cong₂; subst; sym; module ≡-Reasoning)

open import Function
  using (_∘_; _$_; id; flip)
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


2*≡+ : ∀ n → 2 * n ≡ n + n
2*≡+ n =
  2 * n
    ≡⟨⟩
  n + (n + 0)
    ≡⟨ cong (_+_ n) (+-right-identity n) ⟩
  n + n
  ∎
  where open ≡-Reasoning

2*-suc : ∀ n → 2 * (suc n) ≡ suc (suc (2 * n))
2*-suc n =
  2 * (suc n)
    ≡⟨ 2*≡+ (suc n) ⟩
  suc n + suc n
    ≡⟨⟩
  suc (n + suc n)
    ≡⟨ cong suc (+-suc n n) ⟩
  suc (suc (n + n))
    ≡⟨ cong (suc ∘ suc) (sym $ 2*≡+ n) ⟩
  suc (suc (2 * n))
  ∎
  where open ≡-Reasoning

even-2* : ∀ n → Even (2 * n)
even-2* zero =
  even0
even-2* (suc zero) =
  even1 (odd1 even0)
even-2* (suc (suc n)) =
  step $ even-2* n
  where
  open Related.EquationalReasoning hiding (sym)
  step =
    Even (2 * n)
      ∼⟨ even1 ∘ odd1 ⟩
    Even (suc (suc (2 *  n)))
      ≡⟨ cong Even (P.sym $ 2*-suc n) ⟩
    Even (2 * (suc n))
      ∼⟨ even1 ∘ odd1 ⟩
    Even (suc (suc (2 * (suc n))))
      ≡⟨ cong Even (sym $ 2*-suc (suc n)) ⟩
    Even (2 * suc (suc n))
    ∎

even-even+ : ∀ {m n} → Even m → Even (m + n) → Even n
even-even+ even0 even-n =
  even-n
even-even+ (even1 (odd1 {m} even-m)) (even1 (odd1 even+)) =
  even-even+ even-m even+

odd-even* : ∀ {m n} → Odd m → Even (m * n) → Even n
odd-even* (odd1 even0) even-n+0 =
  subst Even (+-right-identity _) even-n+0
odd-even* {_} {n} (odd1 (even1 {m} odd-m)) =
  Even (n + (n + m * n))
    ≡⟨ cong Even (sym $ +-assoc n n (m * n)) ⟩
  Even ((n + n) + m * n)
    ≡⟨ cong (Even ∘ flip _+_ (m * n)) (sym $ 2*≡+ n) ⟩
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
      ≡⟨ 2*≡+ (suc x)  ⟩
    suc x + suc x
      ≡⟨⟩
    suc (x + suc x)
      ≡⟨ cong suc (+-suc x x) ⟩
    suc (suc (x + x))
      ≡⟨ cong suc (sym $ cong suc (2*≡+ x)) ⟩
    suc (suc (2 * x))
      ≡⟨ cong (suc ∘ suc) 2*x≡k ⟩
    suc (suc k)
    ∎

2∣⇒even : ∀ {n} → 2∣ n → Even n
2∣⇒even {n} (x , 2*x≡n) = step $ even-2* x
  where open Related.EquationalReasoning hiding (sym)
        step = Even (2 * x) ≡⟨ cong Even 2*x≡n ⟩ Even n ∎

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

0≢suc : ∀ {n} → 0 ≢ suc n
0≢suc ()

2*≡ : ∀ k n → 2 * k ≡ n → 2 * (1 + k) ≡ 2 + n
2*≡ k n =
  2 * k ≡ n
    ≡⟨ refl ⟩
  k + (k + zero) ≡ n
    ∼⟨ cong (suc ∘ suc) ⟩
  suc (suc (k + (k + zero))) ≡ suc (suc n)
    ∼⟨ subst (λ m → suc m ≡ suc (suc n)) (sym $ +-suc k (k + zero)) ⟩
  suc (k + suc (k + zero)) ≡ suc (suc n)
    ≡⟨ refl ⟩
  2 * (1 + k) ≡ 2 + n
  ∎
  where open Related.EquationalReasoning hiding (sym)

2*s≡ss : ∀ k n → 2 * (1 + k) ≡ 2 + n → 2 * k ≡ n
2*s≡ss k n =
  2 * (1 + k) ≡ 2 + n
    ≡⟨ refl ⟩
  suc (k + suc (k + 0)) ≡ suc (suc n)
    ∼⟨ subst (λ m → suc m ≡ suc (suc n)) (+-suc k (k + zero)) ⟩
  suc (suc (k + (k + 0))) ≡ suc (suc n)
    ∼⟨ cong (pred ∘ pred) ⟩
  k + (k + 0) ≡ n
    ≡⟨ refl ⟩
  2 * k ≡ n
  ∎
  where open Related.EquationalReasoning

2∣? : ∀ n → Dec (∃ λ k → 2 * k ≡ n)
2∣? zero = yes (0 , refl)
2∣? (suc zero) = no help
  where
  help : ∃ (λ k → k + (k + 0) ≡ 1) → ⊥
  help (zero , 0≡1) = 0≢suc 0≡1
  help (suc k , 2+2*k≡1)
    rewrite +-suc k (k + 0)
    = 0≢suc (sym $ cong pred 2+2*k≡1)
2∣? (suc (suc n)) with 2∣? n
... | yes (k , 2*k≡n) =
  yes (suc k , 2*≡ k n 2*k≡n)
... | no ¬2∣n = no (¬2∣n ∘ help)
  where
  help : (∃ λ k → 2 * k ≡ 2 + n) → (∃ λ k′ → 2 * k′ ≡ n)
  help (zero , 0≡2+n) = ⊥-elim (0≢suc 0≡2+n)
  help (suc k , 2*sk≡ssn) = k , 2*s≡ss k n 2*sk≡ssn
