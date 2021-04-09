{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Setoid (Σ : Signature) where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Homomorphism.Base Σ

open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Symmetric)

private
  variable
    a b ℓ₁ ℓ₂ : Level

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  where

  open Setoid ∥ T ∥/≈

  infix 4 _≡ₕ_

  _≡ₕ_ : Rel (S →ₕ T) (a ⊔ ℓ₂)
  f ≡ₕ g = ∀ {x} → ∥ f ∥ₕ x ≈ ∥ g ∥ₕ x

  ≡ₕ-refl : Reflexive _≡ₕ_
  ≡ₕ-refl = refl

  ≡ₕ-sym : Symmetric _≡ₕ_
  ≡ₕ-sym f≈ₕg {x} = sym (f≈ₕg {x})

  ≡ₕ-trans : Transitive _≡ₕ_
  ≡ₕ-trans f≡ₕg g≡ₕh {x} = trans (f≡ₕg {x}) (g≡ₕh {x})

  ≡ₕ-isEquivalence : IsEquivalence _≡ₕ_
  ≡ₕ-isEquivalence = record { refl  = λ {f} → ≡ₕ-refl {f}
                            ; sym   = λ {f g} → ≡ₕ-sym {f} {g}
                            ; trans = λ {f g h} → ≡ₕ-trans {f} {g} {h}
                            }

≡ₕ-setoid : (S : Algebra Σ {a} {ℓ₁})
            → (T : Algebra Σ {b} {ℓ₂})
            → Setoid _ _
≡ₕ-setoid S T = record { Carrier       = S →ₕ T
                       ; _≈_           = _≡ₕ_
                       ; isEquivalence = ≡ₕ-isEquivalence
                       }
