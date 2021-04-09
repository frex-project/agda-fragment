{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Initial (Θ : Theory) where

open import Fragment.Equational.Model Θ
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ)

open import Level using (Level; Setω)

private
  variable
    a ℓ₁ : Level

record IsInitial (M : Model {a} {ℓ₁}) : Setω where
  field

    []_ : ∀ {b ℓ₂} (W : Model {b} {ℓ₂})
          → ∥ M ∥ₐ →ₕ ∥ W ∥ₐ

    universal : ∀ {b ℓ₂} {W : Model {b} {ℓ₂}}
                → (f : ∥ M ∥ₐ →ₕ ∥ W ∥ₐ)
                → f ≡ₕ [] W
