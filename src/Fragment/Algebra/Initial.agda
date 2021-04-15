{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Initial (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ

open import Level using (Level; Setω)

private
  variable
    a ℓ₁ : Level

record IsInitial (A : Algebra {a} {ℓ₁}) : Setω where
  field
    []_ : ∀ {b ℓ₂} (X : Algebra {b} {ℓ₂}) → A ⟿ X

    universal : ∀ {b ℓ₂} {X : Algebra {b} {ℓ₂}}
                → (f : A ⟿ X)
                → f ≗ [] X
