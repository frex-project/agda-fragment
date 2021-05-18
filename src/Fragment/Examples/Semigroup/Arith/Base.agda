{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.Semigroup.Arith.Base where

open import Fragment.Prelude public
open import Data.Nat using (ℕ; _*_; _+_) public
open import Data.Nat.Properties
  using (*-isSemigroup; +-isSemigroup)
open import Relation.Binary.PropositionalEquality public

open ≡-Reasoning public

+-semigroup = semigroup→model +-isSemigroup
*-semigroup = semigroup→model *-isSemigroup
