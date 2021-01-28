{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Equivalence (Σ : Signature) where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Homomorphism.Base Σ
open import Fragment.Algebra.Homomorphism.Properties Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ

open import Level using (Level; _⊔_)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  (S : Algebra Σ {a} {ℓ₁})
  (T : Algebra Σ {b} {ℓ₂})
  where

  infix 3 _≅ₕ_

  record _≅ₕ_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      H   : S →ₕ T
      H⁻¹ : T →ₕ S

      invˡ : H ∘ₕ H⁻¹ ≡ₕ idₕ T
      invʳ : H⁻¹ ∘ₕ H ≡ₕ idₕ S

id-≅ₕ : (S : Algebra Σ {a} {ℓ₁}) → S ≅ₕ S
id-≅ₕ S = record { H    = idₕ S
                 ; H⁻¹  = idₕ S
                 ; invˡ = λ {_} → refl
                 ; invʳ = λ {_} → refl
                 }
  where open Algebra S

flip : ∀ {S : Algebra Σ {a} {ℓ₁}} {T : Algebra Σ {b} {ℓ₂}}
       → S ≅ₕ T → T ≅ₕ S
flip S≅ₕT = record { H    = H⁻¹
                   ; H⁻¹  = H
                   ; invˡ = invʳ
                   ; invʳ = invˡ
                   }
  where open _≅ₕ_ S≅ₕT

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  {U : Algebra Σ {c} {ℓ₃}}
  (T≅ₕU : T ≅ₕ U)
  (S≅ₕT : S ≅ₕ T)
  where

  open _≅ₕ_ T≅ₕU renaming (H to G; H⁻¹ to G⁻¹; invˡ to G-invˡ)
  open _≅ₕ_ S≅ₕT renaming (H to F; H⁻¹ to F⁻¹; invˡ to F-invˡ)

  open import Relation.Binary.Reasoning.Setoid (≡ₕ-setoid U U)

  ∘-≅ₕ-inv : (G ∘ₕ F) ∘ₕ (F⁻¹ ∘ₕ G⁻¹) ≡ₕ idₕ U
  ∘-≅ₕ-inv = begin
      (G ∘ₕ F) ∘ₕ (F⁻¹ ∘ₕ G⁻¹)
    ≈⟨ ∘ₕ-assoc G F (F⁻¹ ∘ₕ G⁻¹) ⟩
      G ∘ₕ (F ∘ₕ (F⁻¹ ∘ₕ G⁻¹))
    ≈⟨ ∘ₕ-congˡ G (F ∘ₕ (F⁻¹ ∘ₕ G⁻¹)) ((F ∘ₕ F⁻¹) ∘ₕ G⁻¹)
                  (∘ₕ-assoc F F⁻¹ G⁻¹) ⟩
      G ∘ₕ ((F ∘ₕ F⁻¹) ∘ₕ G⁻¹)
    ≈⟨ ∘ₕ-congˡ G ((F ∘ₕ F⁻¹) ∘ₕ G⁻¹)
                  (idₕ T ∘ₕ G⁻¹)
                  (∘ₕ-congʳ G⁻¹ (F ∘ₕ F⁻¹) (idₕ T) F-invˡ) ⟩
      G ∘ₕ (idₕ T ∘ₕ G⁻¹)
    ≈⟨ ∘ₕ-congˡ G (idₕ T ∘ₕ G⁻¹) G⁻¹ (idₕ-unitˡ G⁻¹) ⟩
      G ∘ₕ G⁻¹
    ≈⟨ G-invˡ ⟩
      idₕ U
    ∎

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  {U : Algebra Σ {c} {ℓ₃}}
  (T≅ₕU : T ≅ₕ U)
  (S≅ₕT : S ≅ₕ T)
  where

  open _≅ₕ_ T≅ₕU renaming (H to G; H⁻¹ to G⁻¹; invˡ to G-invˡ)
  open _≅ₕ_ S≅ₕT renaming (H to F; H⁻¹ to F⁻¹; invˡ to F-invˡ)

  infix 9 _∘-≅ₕ_

  _∘-≅ₕ_ : S ≅ₕ U
  _∘-≅ₕ_ = record { H    = G ∘ₕ F
                  ; H⁻¹  = F⁻¹ ∘ₕ G⁻¹
                  ; invˡ = ∘-≅ₕ-inv T≅ₕU S≅ₕT
                  ; invʳ = ∘-≅ₕ-inv (flip S≅ₕT) (flip T≅ₕU)
                  }

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Symmetric)

≅ₕ-refl : Reflexive (_≅ₕ_ {a} {ℓ₁} {a} {ℓ₁})
≅ₕ-refl {_} {_} {S} = id-≅ₕ S

≅ₕ-sym : Symmetric (_≅ₕ_ {a} {ℓ₁} {a} {ℓ₁})
≅ₕ-sym = flip

≅ₕ-trans : Transitive (_≅ₕ_ {a} {ℓ₁} {a} {ℓ₁})
≅ₕ-trans S≅ₕT T≅ₕU = T≅ₕU ∘-≅ₕ S≅ₕT

≅ₕ-isEquivalence : IsEquivalence (_≅ₕ_ {a} {ℓ₁} {a} {ℓ₁})
≅ₕ-isEquivalence =
  record { refl  = ≅ₕ-refl
         ; sym   = ≅ₕ-sym
         ; trans = ≅ₕ-trans
         }

≅ₕ-setoid : ∀ {a ℓ} → Setoid _ _
≅ₕ-setoid {a} {ℓ} = record { Carrier       = Algebra Σ {a} {ℓ}
                           ; _≈_           = (_≅ₕ_ {a} {ℓ} {a} {ℓ})
                           ; isEquivalence = ≅ₕ-isEquivalence
                           }
