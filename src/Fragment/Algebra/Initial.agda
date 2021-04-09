{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Initial (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ using (_≡ₕ_)

open import Level using (Level; Setω)

private
  variable
    a ℓ₁ : Level

record IsInitial (S : Algebra {a} {ℓ₁}) : Setω where
  field

    []_ : ∀ {b ℓ₂} (W : Algebra {b} {ℓ₂}) → S →ₕ W

    universal : ∀ {b ℓ₂} {W : Algebra {b} {ℓ₂}}
                → (f : S →ₕ W)
                → f ≡ₕ [] W
