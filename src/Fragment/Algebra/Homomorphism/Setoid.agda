{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Setoid (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism.Base Σ
open import Fragment.Setoid.Morphism

open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

private
  variable
    a b ℓ₁ ℓ₂ : Level

module _
  {S : Algebra {a} {ℓ₁}}
  {T : Algebra {b} {ℓ₂}}
  where

  open Setoid ∥ T ∥/≈

  infix 4 _≗_

  _≗_ : Rel (S ⟿ T) (a ⊔ ℓ₂)
  f ≗ g = ∣ f ∣⃗ ∻ ∣ g ∣⃗

  ≗-refl : ∀ {f} → f ≗ f
  ≗-refl = refl

  ≗-sym : ∀ {f g} → f ≗ g → g ≗ f
  ≗-sym f≗g {x} = sym (f≗g {x})

  ≗-trans : ∀ {f g h} → f ≗ g → g ≗ h → f ≗ h
  ≗-trans f≗g g≗h {x} = trans (f≗g {x}) (g≗h {x})

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = record { refl  = λ {f} → ≗-refl {f}
                           ; sym   = λ {f g} → ≗-sym {f} {g}
                           ; trans = λ {f g h} → ≗-trans {f} {g} {h}
                           }

_⟿_/≗ : Algebra {a} {ℓ₁} → Algebra {b} {ℓ₂} → Setoid _ _
_⟿_/≗ A B = record { Carrier       = A ⟿ B
                    ; _≈_           = _≗_
                    ; isEquivalence = ≗-isEquivalence
                    }
