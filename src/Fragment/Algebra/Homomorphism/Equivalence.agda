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

  infix 3 _≃_

  record _≃_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      _⃗ : S ⟿ T
      _⃖ : T ⟿ S

      invˡ : _⃗ ⊙ _⃖ ≗ id
      invʳ : _⃖ ⊙ _⃗ ≗ id

open _≃_ public

≃-refl : S ≃ S
≃-refl {S = S} = record { _⃗   = id
                        ; _⃖   = id
                        ; invˡ = λ {_} → refl
                        ; invʳ = λ {_} → refl
                        }
  where open Setoid ∥ S ∥/≈

≃-sym : S ≃ T → T ≃ S
≃-sym f = record { _⃗   = f ⃖
                 ; _⃖   = f ⃗
                 ; invˡ = invʳ f
                 ; invʳ = invˡ f
                 }

≃-inv : ∀ (g : T ≃ U) (f : S ≃ T)
        → (g ⃗ ⊙ f ⃗) ⊙ (f ⃖ ⊙ g ⃖) ≗ id
≃-inv {T = T} {U = U} g f = begin
    (g ⃗ ⊙ f ⃗) ⊙ (f ⃖ ⊙ g ⃖)
  ≈⟨ ⊙-assoc (g ⃗) (f ⃗) (f ⃖ ⊙ g ⃖) ⟩
    g ⃗ ⊙ (f ⃗ ⊙ (f ⃖ ⊙ g ⃖))
  ≈⟨ ⊙-congˡ (g ⃗) (f ⃗ ⊙ (f ⃖ ⊙ g ⃖)) ((f ⃗ ⊙ f ⃖) ⊙ g ⃖) (⊙-assoc (f ⃗) (f ⃖) (g ⃖)) ⟩
    g ⃗ ⊙ ((f ⃗ ⊙ f ⃖) ⊙ g ⃖)
  ≈⟨ ⊙-congˡ (g ⃗) ((f ⃗ ⊙ f ⃖) ⊙ g ⃖) (id ⊙ g ⃖) (⊙-congʳ (g ⃖) (f ⃗ ⊙ f ⃖) id (invˡ f)) ⟩
    g ⃗ ⊙ (id ⊙ g ⃖)
  ≈⟨ ⊙-congˡ (g ⃗) (id ⊙ g ⃖) (g ⃖) (id-unitˡ {f = g ⃖}) ⟩
    g ⃗ ⊙ g ⃖
  ≈⟨ invˡ g ⟩
    id
  ∎
  where open import Relation.Binary.Reasoning.Setoid (U ⟿ U /≗)

≃-trans : S ≃ T → T ≃ U → S ≃ U
≃-trans f g = record { _⃗   = g ⃗ ⊙ f ⃗
                     ; _⃖   = f ⃖ ⊙ g ⃖
                     ; invˡ = ≃-inv g f
                     ; invʳ = ≃-inv (≃-sym f) (≃-sym g)
                     }

≃-isEquivalence : IsEquivalence (_≃_ {a} {ℓ₁} {a} {ℓ₁})
≃-isEquivalence =
  record { refl  = ≃-refl
         ; sym   = ≃-sym
         ; trans = ≃-trans
         }

≃-setoid : ∀ {a ℓ} → Setoid _ _
≃-setoid {a} {ℓ} = record { Carrier       = Algebra {a} {ℓ}
                          ; _≈_           = _≃_ {a} {ℓ} {a} {ℓ}
                          ; isEquivalence = ≃-isEquivalence
                          }
