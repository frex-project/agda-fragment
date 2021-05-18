{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.Semigroup.Types where

open import Fragment.Prelude

open import Level using (zero)

open import Function.Related
open import Function.Related.TypeIsomorphisms
  using (×-isSemigroup; ⊎-isSemigroup)
open import Function.Inverse using (_↔_)

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)

×-semigroup = semigroup→model (×-isSemigroup bijection zero)
⊎-semigroup = semigroup→model (⊎-isSemigroup bijection zero)

×-assoc₁ : ∀ {A B C : Set} → (A × (B × C)) ↔ ((A × B) × C)
×-assoc₁ = fragment SemigroupFrex (×-semigroup)

⊎-assoc₁ : ∀ {A B C : Set} → (A ⊎ (B ⊎ C)) ↔ ((A ⊎ B) ⊎ C)
⊎-assoc₁ = fragment SemigroupFrex (⊎-semigroup)
