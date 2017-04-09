module 2IsPrime where

-- Originally written by Nils Anders Danielsson
-- https://lists.chalmers.se/pipermail/agda/2011/003464.html

 open import Data.Empty
 open import Data.Fin as Fin hiding (_+_)
 open import Data.Fin.Dec
 open import Data.Nat
 open import Data.Nat.Divisibility
 open import Data.Unit
 open import Level using (Lift)
 open import Relation.Nullary

 ------------------------------------------------------------------------
 -- Some helpers that should have been in the library

 -- If a decision procedure returns "yes", then we can extract the
 -- proof using from-yes.

 From-yes : ∀ {p} {P : Set p} → Dec P → Set p
 From-yes {P = P} (yes _) = P
 From-yes         (no  _) = Lift ⊤

 from-yes : ∀ {p} {P : Set p} (p : Dec P) → From-yes p
 from-yes (yes p) = p
 from-yes (no  _) = _

 -- If we can decide P, then we can decide its negation.

 decide-negation : ∀ {p} {P : Set p} → Dec P → Dec (¬ P)
 decide-negation (yes p) = no (λ ¬p → ¬p p)
 decide-negation (no ¬p) = yes ¬p

 ------------------------------------------------------------------------
 -- Two is prime

 -- Definition of primality.

 Prime : ℕ → Set
 Prime 0             = ⊥
 Prime 1             = ⊥
 Prime (suc (suc n)) = (i : Fin n) → ¬ (2 + Fin.toℕ i ∣ 2 + n)

 -- Decision procedure for primality.

 prime? : ∀ n → Dec (Prime n)
 prime? 0             = no λ()
 prime? 1             = no λ()
 prime? (suc (suc n)) =
   all? λ i → decide-negation ((2 + Fin.toℕ i) ∣? (2 + n))

 -- 2 is prime.

 2-is-prime : Prime 2
 2-is-prime = from-yes (prime? 2)
