{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Initial (Σ : Signature) where

open import Fragment.Algebra.Algebra

open import Level using (Level; Setω)

private
  variable
    a ℓ₁ : Level

module _
  (S : Algebra Σ {a} {ℓ₁})
  where

  open import Fragment.Algebra.Homomorphism Σ
  open import Fragment.Algebra.Homomorphism.Setoid Σ using (_≡ₕ_)

  record IsInitial : Setω where
    field

      []_ : ∀ {b ℓ₂} (W : Algebra Σ {b} {ℓ₂}) → S →ₕ W

      universal : ∀ {b ℓ₂} {W : Algebra Σ {b} {ℓ₂}}
                  → (F : S →ₕ W)
                  → F ≡ₕ [] W
