{-# OPTIONS --without-K --exact-split --safe #-}

module Fragment.Setoid.Morphism.Setoid where

open import Fragment.Setoid.Morphism.Base

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid; IsEquivalence; Rel)

private
  variable
    a b ℓ₁ ℓ₂ : Level

module _ {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} where

  open Setoid T

  infix 4 _≗_

  _≗_ : Rel (S ↝ T) (a ⊔ ℓ₂)
  f ≗ g = ∀ {x} → ∣ f ∣ x ≈ ∣ g ∣ x

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

_↝_/≗ : Setoid a ℓ₁ → Setoid b ℓ₂ → Setoid _ _
S ↝ T /≗ = record { Carrier       = S ↝ T
                  ; _≈_           = _≗_
                  ; isEquivalence = ≗-isEquivalence
                  }
