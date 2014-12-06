module NatStar where

data NatStar : Set where
  one  : NatStar
  suc : NatStar -> NatStar

-- copy oparators from the Agda standard library
-- Data.Nat
infixl 6 _+_

_+_ : NatStar -> NatStar -> NatStar
one + n = suc n
suc m + n = suc (m + n)

_*_ : NatStar -> NatStar -> NatStar
one * n = n
suc m * n = n + m * n

