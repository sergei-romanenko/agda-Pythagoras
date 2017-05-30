module 2IsPrime where

-- Originally written by Nils Anders Danielsson
-- https://lists.chalmers.se/pipermail/agda/2011/003464.html

-- Now this stuff is in Data.Nat.Primality

 open import Data.Empty
   using (⊥)
 open import Data.Fin as Fin
   using(Fin; toℕ)
 open import Data.Fin.Dec
   using (all?)
 open import Data.Nat
   using (ℕ; _+_; zero; suc)
 open import Data.Nat.Divisibility
   using (_∣_; _∣?_)
 open import Relation.Nullary
   using (¬_; yes; no)
 open import Relation.Nullary.Decidable
   using (From-yes; from-yes)
 open import Relation.Nullary.Negation
   using (¬?)
 open import Relation.Unary
   using (Decidable)

 -- Definition of primality.

 Prime : ℕ → Set
 Prime 0 = ⊥
 Prime 1 = ⊥
 Prime (suc (suc n)) =
   (i : Fin n) → ¬ (2 + toℕ i ∣ 2 + n)

 -- Decision procedure for primality.

 prime? : Decidable Prime
 prime? 0 = no λ()
 prime? 1 = no λ()
 prime? (suc (suc n)) =
   all? (λ i → ¬? ((2 + toℕ i) ∣? 2 + n))

 -- 2 is prime.

 2-is-prime : Prime 2
 2-is-prime = from-yes (prime? 2)
