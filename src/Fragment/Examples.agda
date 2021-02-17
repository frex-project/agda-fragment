{-# OPTIONS --without-K --safe #-}

module Fragment.Examples where

{-
open import Fragment.Equational.Bundles using (Θ-semigroup)
open import Fragment.Equational.Model
open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.Structures using (semigroup→isModel)

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-isSemigroup)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

+-isModel : IsModel Θ-semigroup (PE.setoid ℕ)
+-isModel = (semigroup→isModel (PE.setoid ℕ) +-isSemigroup)

open import Fragment.Extensions.Semigroup +-isModel

simple : ∀ {m n} → (m + 2) + (3 + n) ≡ (m + 5) + n
simple {m = m} {n = n} = fundamental (++-isFrex {n = 2}) p θ
    where θ : Fin 2 → ℕ
          θ zero       = m
          θ (suc zero) = n
          term = normalise (consD (# 0) (consS 2 (leaf (inj₂ (# 1)))))
          p = PE.refl {x = term , normalise-reduction {x = term}}
-}
