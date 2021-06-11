{-# OPTIONS --without-K --exact-split --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Definitions (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)
open import Data.Vec using (Vec; map)

open import Function using (Congruent) public

private
  variable
    a b ℓ₁ ℓ₂ : Level

Homomorphic : (S : Algebra {a} {ℓ₁}) (T : Algebra {b} {ℓ₂})
              → (∥ S ∥ → ∥ T ∥) → Set (a ⊔ ℓ₂)
Homomorphic S T h = ∀ {arity} → (f : ops Σ arity)
                    → (xs : Vec ∥ S ∥ arity)
                    → T ⟦ f ⟧ (map h xs) =[ T ] h (S ⟦ f ⟧ xs)
