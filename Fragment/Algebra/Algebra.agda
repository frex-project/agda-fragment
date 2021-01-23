{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Algebra (Σ : Signature) where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level

module _ (S : Setoid a ℓ) where

  open import Data.Vec
  open import Data.Vec.Relation.Binary.Equality.Setoid S using (_≋_)

  open Setoid S renaming (Carrier to A)

  Interpretation : Set a
  Interpretation = ∀ {arity} → (f : ops Σ arity) → Vec A arity → A

  Congruence : Interpretation → Set (a ⊔ ℓ)
  Congruence ⟦_⟧ = ∀ {arity}
                   → (f : ops Σ arity)
                   → ∀ {xs ys} → xs ≋ ys → ⟦ f ⟧ xs ≈ ⟦ f ⟧ ys

  record IsAlgebra : Set (a ⊔ ℓ) where
    field
      ⟦_⟧     : Interpretation
      ⟦⟧-cong : Congruence ⟦_⟧

record Algebra : Set (suc a ⊔ suc ℓ) where
  field
    Carrierₛ  : Setoid a ℓ
    isAlgebra : IsAlgebra Carrierₛ

  open Setoid Carrierₛ public
  open IsAlgebra isAlgebra public
