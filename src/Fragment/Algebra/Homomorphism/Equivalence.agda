{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Equivalence (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism.Base Σ
open import Fragment.Algebra.Homomorphism.Properties Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Symmetric)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level
    S : Algebra {a} {ℓ₁}
    T : Algebra {b} {ℓ₂}
    U : Algebra {c} {ℓ₃}

module _
  (S : Algebra {a} {ℓ₁})
  (T : Algebra {b} {ℓ₂})
  where

  infix 3 _≅ₕ_

  record _≅ₕ_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ∥_∥ₑ   : S →ₕ T
      ∥_∥ₑ⁻¹ : T →ₕ S

      ∥_∥ₑ-invˡ : ∥_∥ₑ ∘ₕ ∥_∥ₑ⁻¹ ≡ₕ idₕ
      ∥_∥ₑ-invʳ : ∥_∥ₑ⁻¹ ∘ₕ ∥_∥ₑ ≡ₕ idₕ

open _≅ₕ_ public

idₑ : (S : Algebra {a} {ℓ₁}) → S ≅ₕ S
idₑ S = record { ∥_∥ₑ      = idₕ
               ; ∥_∥ₑ⁻¹    = idₕ
               ; ∥_∥ₑ-invˡ = λ {_} → refl
               ; ∥_∥ₑ-invʳ = λ {_} → refl
               }
  where open Setoid ∥ S ∥/≈

flip : S ≅ₕ T → T ≅ₕ S
flip f = record { ∥_∥ₑ      = ∥ f ∥ₑ⁻¹
                ; ∥_∥ₑ⁻¹    = ∥ f ∥ₑ
                ; ∥_∥ₑ-invˡ = ∥ f ∥ₑ-invʳ
                ; ∥_∥ₑ-invʳ = ∥ f ∥ₑ-invˡ
                }

∘ₑ-inv : ∀ (g : T ≅ₕ U) (f : S ≅ₕ T)
         → (∥ g ∥ₑ ∘ₕ ∥ f ∥ₑ) ∘ₕ (∥ f ∥ₑ⁻¹ ∘ₕ ∥ g ∥ₑ⁻¹) ≡ₕ idₕ
∘ₑ-inv {T = T} {U = U} g f = begin
    (∥ g ∥ₑ ∘ₕ ∥ f ∥ₑ) ∘ₕ (∥ f ∥ₑ⁻¹ ∘ₕ ∥ g ∥ₑ⁻¹)
  ≈⟨ ∘ₕ-assoc ∥ g ∥ₑ ∥ f ∥ₑ (∥ f ∥ₑ⁻¹ ∘ₕ ∥ g ∥ₑ⁻¹) ⟩
    ∥ g ∥ₑ ∘ₕ (∥ f ∥ₑ ∘ₕ (∥ f ∥ₑ⁻¹ ∘ₕ ∥ g ∥ₑ⁻¹))
  ≈⟨ ∘ₕ-congˡ ∥ g ∥ₑ
              (∥ f ∥ₑ ∘ₕ (∥ f ∥ₑ⁻¹ ∘ₕ ∥ g ∥ₑ⁻¹))
              ((∥ f ∥ₑ ∘ₕ ∥ f ∥ₑ⁻¹) ∘ₕ ∥ g ∥ₑ⁻¹)
              (∘ₕ-assoc ∥ f ∥ₑ ∥ f ∥ₑ⁻¹ ∥ g ∥ₑ⁻¹) ⟩
    ∥ g ∥ₑ ∘ₕ ((∥ f ∥ₑ ∘ₕ ∥ f ∥ₑ⁻¹) ∘ₕ ∥ g ∥ₑ⁻¹)
  ≈⟨ ∘ₕ-congˡ ∥ g ∥ₑ
              ((∥ f ∥ₑ ∘ₕ ∥ f ∥ₑ⁻¹) ∘ₕ ∥ g ∥ₑ⁻¹)
              (idₕ ∘ₕ ∥ g ∥ₑ⁻¹)
              (∘ₕ-congʳ ∥ g ∥ₑ⁻¹ (∥ f ∥ₑ ∘ₕ ∥ f ∥ₑ⁻¹) idₕ ∥ f ∥ₑ-invˡ) ⟩
    ∥ g ∥ₑ ∘ₕ (idₕ ∘ₕ ∥ g ∥ₑ⁻¹)
  ≈⟨ ∘ₕ-congˡ ∥ g ∥ₑ (idₕ ∘ₕ ∥ g ∥ₑ⁻¹) ∥ g ∥ₑ⁻¹ (idₕ-unitˡ ∥ g ∥ₑ⁻¹) ⟩
    ∥ g ∥ₑ ∘ₕ ∥ g ∥ₑ⁻¹
  ≈⟨ ∥ g ∥ₑ-invˡ ⟩
    idₕ
  ∎
  where open import Relation.Binary.Reasoning.Setoid (≡ₕ-setoid U U)

infix 9 _∘ₑ_

_∘ₑ_ : T ≅ₕ U → S ≅ₕ T → S ≅ₕ U
g ∘ₑ f = record { ∥_∥ₑ      = ∥ g ∥ₑ ∘ₕ ∥ f ∥ₑ
                ; ∥_∥ₑ⁻¹    = ∥ f ∥ₑ⁻¹ ∘ₕ ∥ g ∥ₑ⁻¹
                ; ∥_∥ₑ-invˡ = ∘ₑ-inv g f
                ; ∥_∥ₑ-invʳ = ∘ₑ-inv (flip f) (flip g)
                }

≅ₕ-refl : Reflexive (_≅ₕ_ {a} {ℓ₁} {a} {ℓ₁})
≅ₕ-refl {_} {_} {S} = idₑ S

≅ₕ-sym : Symmetric (_≅ₕ_ {a} {ℓ₁} {a} {ℓ₁})
≅ₕ-sym = flip

≅ₕ-trans : Transitive (_≅ₕ_ {a} {ℓ₁} {a} {ℓ₁})
≅ₕ-trans f g = g ∘ₑ f

≅ₕ-isEquivalence : IsEquivalence (_≅ₕ_ {a} {ℓ₁} {a} {ℓ₁})
≅ₕ-isEquivalence =
  record { refl  = ≅ₕ-refl
         ; sym   = ≅ₕ-sym
         ; trans = ≅ₕ-trans
         }

≅ₕ-setoid : ∀ {a ℓ} → Setoid _ _
≅ₕ-setoid {a} {ℓ} = record { Carrier       = Algebra {a} {ℓ}
                           ; _≈_           = _≅ₕ_ {a} {ℓ} {a} {ℓ}
                           ; isEquivalence = ≅ₕ-isEquivalence
                           }
