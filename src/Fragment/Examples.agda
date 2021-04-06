{-# OPTIONS --without-K --safe #-}

module Fragment.Examples where

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-isSemigroup)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Fragment.Prelude

simple : ∀ {m n} → (m + 2) + (3 + n) ≡ (m + 5) + n
simple {m} {n} = fragment SemigroupFrex
                          (semigroup→model (PE.setoid ℕ) +-isSemigroup)
                          ((m + 2) + (3 + n))
                          ((m + 5) + n)
