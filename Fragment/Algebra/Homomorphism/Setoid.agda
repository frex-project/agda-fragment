{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra

module Fragment.Algebra.Homomorphism.Setoid
  {a b ℓ₁ ℓ₂}
  (Σ : Signature)
  (S : Algebra Σ {a} {ℓ₁})
  (T : Algebra Σ {b} {ℓ₂})
  where

open import Fragment.Algebra.Homomorphism.Base Σ

open import Level using (_⊔_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Symmetric)

open Algebra T

infix 4 _≡ₕ_

_≡ₕ_ : Rel (S →ₕ T) (a ⊔ ℓ₂)
F ≡ₕ G = ∀ {x} → applyₕ F x ≈ applyₕ G x


≡ₕ-refl : Reflexive _≡ₕ_
≡ₕ-refl = refl

≡ₕ-sym : Symmetric _≡ₕ_
≡ₕ-sym F≈ₕG {x} = sym (F≈ₕG {x})

≡ₕ-trans : Transitive _≡ₕ_
≡ₕ-trans F≡ₕG G≡ₕH {x} = trans (F≡ₕG {x}) (G≡ₕH {x})

≡ₕ-isEquivalence : IsEquivalence _≡ₕ_
≡ₕ-isEquivalence = record { refl  = λ {F} → ≡ₕ-refl {F}
                          ; sym   = λ {F G} → ≡ₕ-sym {F} {G}
                          ; trans = λ {F G H} → ≡ₕ-trans {F} {G} {H}
                          }

≡ₕ-setoid : Setoid _ _
≡ₕ-setoid = record { Carrier       = S →ₕ T
                   ; _≈_           = _≡ₕ_
                   ; isEquivalence = ≡ₕ-isEquivalence
                   }
