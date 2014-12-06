module Corollary where

open import Algebra
open import Function
import Algebra.FunctionProperties as FunctionProperties
open FunctionProperties
open import Algebra.Structures
open import Agda.Primitive
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
  as PropEq
open PropEq.≡-Reasoning

open import NatStar
open import NatStarProperties

import Cancel
open Cancel {_} {_} {NatStar} (_≡_)
open import CancellativeAbelianMonoid

isCancellativeAbelianMonoid : 
  IsCancellativeAbelianMonoid _≡_ _*_ one
isCancellativeAbelianMonoid
  = record {
      isCommutativeMonoid = *-isCommutativeMonoid
    ; cancel = cancel-*-left
    }

m : CancellativeAbelianMonoid lzero lzero
m = record {
      Carrier = NatStar
    ; _≈_ = _≡_
    ; _∙_ = _*_
    ; ε   = one
    ; isCancellativeAbelianMonoid = isCancellativeAbelianMonoid
    }

open import Noether
import Property
open Property lzero lzero m
import Theorem 
open Theorem lzero m

-- the original proof of 'two is prime' is written
-- by Nils Anders Danielsson
-- https://lists.chalmers.se/pipermail/agda/2011/003464.html

-- lemma1 : 2 isPrime
-- lemma1 = {!!}
postulate lemma1 : (suc one) isPrime

-- lemma2 : Noether Carrier (multiple 2)
-- lemma2 = {!!}
postulate lemma2 : Noether Carrier (multiple (suc one))

corollary : (suc one) isNotSquare
corollary = theorem (suc one) lemma1 lemma2

