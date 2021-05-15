{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.Product where

{-
open import Level using (suc)
open import Function.Related
open import Algebra
open import Function.Related.TypeIsomorphisms using (×-isSemigroup; ×-comm)
open import Function.Inverse as Inv using (_↔_)
open import Data.Product using (_×_)

×-isCommutativeSemigroup : ∀ k ℓ → IsCommutativeSemigroup {suc ℓ} (Related ⌊ k ⌋) _×_
×-isCommutativeSemigroup k ℓ = record { isSemigroup = ×-isSemigroup k ℓ
                                      ; comm        = λ _ _ → ↔⇒ (×-comm _ _)
                                      }

open import Fragment.Prelude

simple : ∀ {k ℓ} {A B C : Set ℓ} → ((A × (B × C)) × A) ↔ ((A × A) × (B × C))
simple =
  fragment CSemigroupFrex
           (csemigroup→model (×-isCommutativeSemigroup _ _))

simple : ∀ {k ℓ} {A B C : Set ℓ} → ((A × (B × C)) × A) ↔ ((A × A) × (B × C))
simple {k} {_} {A} {B} {C} =
  frexify Θ-csemigroup
          CSemigroupFrex
          (×-model _ _)
          (A ∷ B ∷ C ∷ [])
          {lhs = (⟨ # 0 ⟩ ⟨ • ⟩₂ (⟨ # 1 ⟩ ⟨ • ⟩₂ ⟨ # 2 ⟩)) ⟨ • ⟩₂ ⟨ # 0 ⟩ }
          {rhs = (⟨ # 0 ⟩ ⟨ • ⟩₂ ⟨ # 0 ⟩) ⟨ • ⟩₂ (⟨ # 1 ⟩ ⟨ • ⟩₂ ⟨ # 2 ⟩)}
          (Setoid.refl ∥ FreeExtension._[_] CSemigroupFrex (×-model _ _) 3 ∥/≈)
  where open import Fragment.Algebra.Free.Syntax Σ-magma (SK-setoid k _)
-}
