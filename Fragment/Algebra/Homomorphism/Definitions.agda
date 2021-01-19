{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Definitions (Σ : Signature) where

open import Fragment.Algebra.Algebra

open import Level using (Level; _⊔_)

private
  variable
    a b ℓ₁ ℓ₂ : Level

module _
  (S : Algebra Σ {a} {ℓ₁})
  (T : Algebra Σ {b} {ℓ₂})
  where

  open Algebra S renaming (Carrier to A; _≈_ to _≈ₛ_; ⟦_⟧ to S⟦_⟧)
  open Algebra T renaming (Carrier to B; _≈_ to _≈ₜ_; ⟦_⟧ to T⟦_⟧)

  open import Data.Vec using (Vec; map)

  open import Function.Definitions using (Congruent) public

  Homomorphic : (A → B) → Set (a ⊔ ℓ₂)
  Homomorphic h = ∀ {arity} → (f : ops Σ arity)
                  → (xs : Vec A arity)
                  → T⟦ f ⟧ (map h xs) ≈ₜ h (S⟦ f ⟧ xs)
