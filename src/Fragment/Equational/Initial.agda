{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Initial (Θ : Theory) where

open import Fragment.Equational.Model Θ
open import Fragment.Algebra.Homomorphism (Σ Θ)

open import Level using (Level; Setω)

private
  variable
    a ℓ₁ : Level

record IsInitial (A : Model {a} {ℓ₁}) : Setω where
  field
    []_ : ∀ {b ℓ₂} (X : Model {b} {ℓ₂})
          → ∥ A ∥ₐ ⟿ ∥ X ∥ₐ

    universal : ∀ {b ℓ₂} {X : Model {b} {ℓ₂}}
                → (f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ)
                → f ≗ [] X
