{-
  This has been produced by rewriting the Coq code by
  Pierre Corbineau in
    http://www-verimag.imag.fr/~corbinea/ftp/programs/sqrt2.v

  There is no m and n such that
    n ≢ 0 and m^2 ≡ 2*n^2
  Hence, sqrt 2 is irrational.
-}

module Corbineau.Sqrt2 where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; ⌊_/2⌋; _<′_; ≤′-refl; _≟_)
open import Data.Nat.Properties.Simple
  using (+-suc; +-assoc; *-comm; distribʳ-*-+; +-right-identity)
open import Data.Nat.Properties
  using (s≤′s; ⌊n/2⌋≤′n)
open import Data.Sum as Sum
  using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Empty
  using (⊥; ⊥-elim)

open import Function
  using (_∘_; _$_)
import Function.Related as Related

open import Relation.Nullary
  using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; cong; cong₂; subst; sym; module ≡-Reasoning)

open import Induction.WellFounded
  using (Acc; acc)
open import Induction.Nat
  using (<-well-founded)

infixr 8 2*_
infixl 9 _^2

2*_ : ℕ → ℕ
2* n = n + n

_^2 : ℕ → ℕ
n ^2 = n * n

2*-suc : ∀ n → 2* (suc n) ≡ suc (suc (2* n))
2*-suc n =
  2* (suc n)
    ≡⟨⟩
  suc (n + suc n)
    ≡⟨ cong suc (+-suc n n) ⟩
  suc (suc (n + n))
    ≡⟨⟩
  suc (suc (2* n))
  ∎
  where open ≡-Reasoning

[2*]/2 : ∀ n → ⌊ 2* n /2⌋ ≡ n
[2*]/2 zero = refl
[2*]/2 (suc n) = begin
  ⌊ 2* (suc n) /2⌋
    ≡⟨ cong ⌊_/2⌋ (2*-suc n) ⟩
  ⌊ suc (suc (2* n)) /2⌋
    ≡⟨⟩
  suc ⌊ (2* n) /2⌋
    ≡⟨ cong suc ([2*]/2 n) ⟩
  suc n
  ∎
  where open ≡-Reasoning

2*-inj : ∀ {m n} → 2* m ≡ 2* n → m ≡ n
2*-inj {m} {n} 2*m≡2*n = begin
  m
    ≡⟨ sym $ [2*]/2 m ⟩
  ⌊ 2* m /2⌋
    ≡⟨ cong ⌊_/2⌋ 2*m≡2*n ⟩
  ⌊ 2* n /2⌋
    ≡⟨ [2*]/2 n ⟩
  n
  ∎
  where open ≡-Reasoning

2*-*-left : ∀ m n → 2* (m * n) ≡ m * (2* n)
2*-*-left m n = begin
  2* (m * n)
    ≡⟨ cong 2*_ (*-comm m n) ⟩
  2* (n * m)
    ≡⟨⟩
  n * m + n * m
    ≡⟨ sym $ distribʳ-*-+ m n n ⟩
  (n + n) * m
    ≡⟨ *-comm (n + n) m ⟩
  m * (n + n)
    ≡⟨⟩
  m * (2* n)
  ∎
  where open ≡-Reasoning

2*-*-right : ∀ m n → 2* (m * n) ≡ (2* m) * n
2*-*-right m n = begin
  2* (m * n)
    ≡⟨ cong 2*_ (*-comm m n) ⟩
  2* (n * m)
    ≡⟨ 2*-*-left n m ⟩
  n * (2* m)
    ≡⟨ *-comm n (2* m) ⟩
  (2* m) * n
  ∎
  where open ≡-Reasoning

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

even-2* : ∀ n → Even (2* n)
even-2* zero =
  even0
even-2* (suc zero) =
  even1 (odd1 even0)
even-2* (suc (suc n)) =
  step $ even-2* n
  where
  open Related.EquationalReasoning hiding (sym)
  step =
    Even (2* n)
      ∼⟨ even1 ∘ odd1 ⟩
    Even (suc (suc (2*  n)))
      ≡⟨ cong Even (P.sym $ 2*-suc n) ⟩
    Even (2* (suc n))
      ∼⟨ even1 ∘ odd1 ⟩
    Even (suc (suc (2* (suc n))))
      ≡⟨ cong Even (sym $ 2*-suc (suc n)) ⟩
    Even (2* suc (suc n))
    ∎

even-2*/2 : ∀ {n} → Even n → 2* ⌊ n /2⌋ ≡ n
even-2*/2 even0 = refl
even-2*/2 (even1 (odd1 {n} even-n)) = begin
  2* (suc ⌊ n /2⌋)
    ≡⟨ 2*-suc ⌊ n /2⌋ ⟩
  suc (suc (2* ⌊ n /2⌋))
    ≡⟨ cong (suc ∘ suc) (even-2*/2 even-n) ⟩
  suc (suc n)
  ∎
  where open ≡-Reasoning

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
    ∼⟨ subst Even (P.sym $ +-assoc n n (m * n)) ⟩
  Even ((n + n) + m * n)
    ∼⟨ even-even+ (even-2* n) ⟩
  Even (m * n)
    ∼⟨ odd-even* odd-m ⟩
  Even n
  ∎
  where open Related.EquationalReasoning

even^2 : ∀ {n} → Even (n ^2) → Even n
even^2 {n} even* with even⊎odd n
... | inj₁ even-n = even-n
... | inj₂ odd-n = odd-even* odd-n even*

odd-2*/2 : ∀ {n} → Odd n → suc (2* ⌊ n /2⌋) ≡ n
odd-2*/2 (odd1 even0) = refl
odd-2*/2 (odd1 (even1 {n} odd-n)) =
  suc (2* (suc ⌊ n /2⌋))
    ≡⟨ cong suc (2*-suc ⌊ n /2⌋) ⟩
  suc (suc (suc (2* ⌊ n /2⌋)))
    ≡⟨ cong (suc ∘ suc) (odd-2*/2 odd-n) ⟩
  suc (suc n)
  ∎
  where open ≡-Reasoning

even-4*[/2^2] : ∀ n → Even n → 2* 2* (⌊ n /2⌋ ^2) ≡ n ^2
even-4*[/2^2] n even-n = begin
  2* 2* (⌊ n /2⌋ * ⌊ n /2⌋)
    ≡⟨ cong 2*_ (2*-*-left ⌊ n /2⌋ ⌊ n /2⌋) ⟩
  2* (⌊ n /2⌋ * 2* ⌊ n /2⌋)
    ≡⟨ 2*-*-right ⌊ n /2⌋ (2* ⌊ n /2⌋) ⟩
  (2* ⌊ n /2⌋) * (2* ⌊ n /2⌋)
    ≡⟨ cong₂ _*_ (even-2*/2 even-n) (even-2*/2 even-n) ⟩
  n ^2
  ∎
  where open ≡-Reasoning

^2-≡0 :  ∀ {n} → n ^2 ≡ 0 → n ≡ 0
^2-≡0 {zero} n^2≡0 = refl
^2-≡0 {suc n} ()

/2<′ : ∀ n → n ≢ 0 → ⌊ n /2⌋ <′ n
/2<′ zero n≢0 = ⊥-elim (n≢0 refl)
/2<′ (suc zero) n≢0 = ≤′-refl
/2<′ (suc (suc n)) n≢0 =
  s≤′s (s≤′s (⌊n/2⌋≤′n n))

--
-- The most sophisticated part:
--   m^2 ≡ 2*p^2 ⇒ p ≡ 0.
-- The proof is by reducing the problem to a "smaller" one:
--   (m/2)^2 ≡ 2*(p/2)^2 ⇒ p/2 ≡ 0
--

descent : ∀ m p → m ^2 ≡ 2* (p ^2) → Acc _<′_ m → p ≡ 0

descent m p m^2≡2*p^2 a with m ≟ 0

descent m p m^2≡2*p^2 a | yes m≡0 rewrite m≡0 =
  2* (p ^2) ≡ 0 ∼⟨ 2*-inj ⟩ p ^2 ≡ 0 ∼⟨ ^2-≡0 ⟩ p ≡ 0
  ∎ $ P.sym m^2≡2*p^2
  where open Related.EquationalReasoning

descent m p m^2≡2*p^2 (acc rs) | no m≢0 =
  p≡0
  where

  n = ⌊ m /2⌋
  q = ⌊ p /2⌋

  even-m : Even m
  even-m =
    Even (2* (p ^2))
      ≡⟨ cong Even (P.sym $ m^2≡2*p^2) ⟩
    Even (m ^2)
      ∼⟨ even^2 ⟩
    Even m
    ∎ $ even-2* (p ^2)
    where open Related.EquationalReasoning

  4*n^2≡m^2 : 2* 2* (n ^2) ≡ m ^2
  4*n^2≡m^2 = even-4*[/2^2] m even-m

  4*n^2≡2*p^2 : 2* 2* (n ^2) ≡ 2* (p ^2)
  4*n^2≡2*p^2 = begin
    2* 2* (n ^2) ≡⟨ 4*n^2≡m^2 ⟩ m ^2 ≡⟨ m^2≡2*p^2 ⟩ 2* (p ^2) ∎
    where open ≡-Reasoning

  2*n^2≡p^2 : 2* (n ^2) ≡ p ^2
  2*n^2≡p^2 = 2*-inj 4*n^2≡2*p^2

  even-p : Even p
  even-p =
    Even (2* (n ^2))
      ≡⟨ cong Even  2*n^2≡p^2  ⟩
    Even (p ^2)
      ∼⟨ even^2 ⟩
    Even p
    ∎ $ even-2* (n ^2)
    where open Related.EquationalReasoning

  4*n^2≡8*q^2 : 2* 2* (n ^2) ≡ 2* 2* 2* (q ^2)
  4*n^2≡8*q^2 = begin
    2* 2* (n ^2)
      ≡⟨ 4*n^2≡2*p^2 ⟩
    2* (p ^2)
      ≡⟨ cong 2*_ (sym $ even-4*[/2^2] p even-p) ⟩
    2* (2* 2* (q ^2))
    ∎
    where open ≡-Reasoning

  n^2≡2*q^2 : n ^2 ≡ 2* (q ^2)
  n^2≡2*q^2 = 2*-inj (2*-inj 4*n^2≡8*q^2)

  q≡0 : q ≡ 0
  q≡0 = descent n q n^2≡2*q^2 (rs n (/2<′ m m≢0))

  p≡0 : p ≡ 0
  p≡0 = begin
    p ≡⟨ sym $ even-2*/2 even-p ⟩ 2* q ≡⟨ cong 2*_ q≡0 ⟩ 2* 0 ≡⟨⟩ 0 ∎
    where open ≡-Reasoning

--  There is no m and n such that
--    n ≢ 0 and m^2 ≡ 2*n^2
--  Hence, sqrt 2 is irrational.

irrational-sqrt2 : ∀ m n → n ≢ 0 → ¬ (m ^2 ≡ 2* (n ^2))
irrational-sqrt2 m n n≢0 m^2≡2*n^2 =
  n≢0 n≡0
  where n≡0 : n ≡ 0
        n≡0 = descent m n m^2≡2*n^2 (<-well-founded m)
