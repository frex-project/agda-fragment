{-# OPTIONS --without-K --safe #-}

module Fragment.Examples where

open import Fragment.Equational.Bundles using (Θ-semigroup)
open import Fragment.Equational.Model using (Model; IsModel)
open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.Structures using (semigroup→isModel)

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-isSemigroup; +-assoc)

open import Algebra.Structures using (IsSemigroup)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

+-isModel : IsModel Θ-semigroup (PE.setoid ℕ)
+-isModel = semigroup→isModel (PE.setoid ℕ) +-isSemigroup

+-model : Model Θ-semigroup
+-model = record { isModel = +-isModel; Carrierₛ = PE.setoid ℕ }

simple : ∀ {m n} → (m + 2) + (3 + n) ≡ (m + 5) + n
simple {m} {n} = fragment +-model ++-isFrex
                          ((m + 2) + (3 + n))
                          ((m + 5) + n)
  where open import Fragment.Extensions.Semigroup +-isModel 2
        open import Fragment.Macros.Destructure
