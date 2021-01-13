{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Rel; IsEquivalence)

module Fragment.Algebra.Algebra
  {a ℓ}
  (S : Setoid a ℓ)
  where

open import Level using (_⊔_)
open import Data.Vec
open import Data.Vec.Relation.Binary.Equality.Setoid S using (_≋_)

open import Fragment.Algebra.Signature

open Setoid S renaming (Carrier to A)

Interpretation : Signature → Set a
Interpretation Σ = ∀ {arity} → (f : ops Σ arity) → Vec A arity → A

Congruence : (Σ : Signature) → (Interpretation Σ) → Set (a ⊔ ℓ)
Congruence Σ ⟦_⟧ = ∀ {arity}
                   → (f : ops Σ arity)
                   → ∀ {xs ys} → xs ≋ ys → ⟦ f ⟧ xs ≈ ⟦ f ⟧ ys

record IsAlgebra (Σ : Signature) : Set (a ⊔ ℓ) where
  field
    ⟦_⟧     : Interpretation Σ
    ⟦⟧-cong : Congruence Σ ⟦_⟧
