{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra

module Fragment.Algebra.Homomorphism
  {a b ℓ₁ ℓ₂ Σ}
  {S : Setoid a ℓ₁}
  {T : Setoid b ℓ₂}
  (Sᴬ : IsAlgebra S Σ)
  (Tᴬ : IsAlgebra T Σ)
  where

open import Level using (_⊔_)
open import Data.Vec

open Setoid S renaming (Carrier to A; _≈_ to _≈ₛ_)
open Setoid T renaming (Carrier to B; _≈_ to _≈ₜ_)

open IsAlgebra Sᴬ renaming (⟦_⟧ to S⟦_⟧)
open IsAlgebra Tᴬ renaming (⟦_⟧ to T⟦_⟧)

record Homomorphism : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    h     : A → B
    h-hom : ∀ {arity} → (f : ops Σ arity)
            → (xs : Vec A arity)
            → T⟦ f ⟧ (map h xs) ≈ₜ h (S⟦ f ⟧ xs)
