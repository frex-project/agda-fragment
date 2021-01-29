{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Base (Σ : Signature) where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Homomorphism.Definitions Σ

open import Level using (Level; _⊔_)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  (S : Algebra Σ {a} {ℓ₁})
  (T : Algebra Σ {b} {ℓ₂})
  where

  open Algebra S renaming (Carrier to A; _≈_ to _≈ₛ_)
  open Algebra T renaming (Carrier to B; _≈_ to _≈ₜ_)

  record _→ₕ_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      h      : A → B
      h-cong : Congruent _≈ₛ_ _≈ₜ_ h
      h-hom  : Homomorphic S T h

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  (F : S →ₕ T)
  where

  open Algebra S renaming (Carrier to A)
  open Algebra T renaming (Carrier to B)

  open _→ₕ_ F renaming (h to f)

  applyₕ : A → B
  applyₕ x = f x

module _ (S : Algebra Σ {a} {ℓ₁}) where

  open Algebra S

  open import Function using (id; _$_)
  open import Relation.Binary using (IsEquivalence)
  open import Data.Vec.Properties using (map-id)
  open import Data.Vec.Relation.Binary.Equality.Setoid Carrierₛ

  id-cong : Congruent _≈_ _≈_ id
  id-cong x≈y = x≈y

  id-hom : Homomorphic S S id
  id-hom {n} f xs =
    ⟦⟧-cong f $ IsEquivalence.reflexive (≋-isEquivalence n) (map-id xs)

  idₕ : S →ₕ S
  idₕ = record { h      = id
               ; h-cong = id-cong
               ; h-hom  = id-hom
               }

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  {U : Algebra Σ {c} {ℓ₃}}
  (H : T →ₕ U)
  (G : S →ₕ T)
  where

  open Algebra S renaming (Carrier to A; _≈_ to _≈ₛ_; ⟦_⟧ to S⟦_⟧)
  open Algebra T renaming (Carrier to B; _≈_ to _≈ₜ_; ⟦_⟧ to T⟦_⟧)
  open Algebra U
    renaming ( Carrier       to C
             ; _≈_           to _≈ᵤ_
             ; Carrierₛ      to Cₛ
             ; isEquivalence to ≈ᵤ-isEquivalence
             ; ⟦_⟧           to U⟦_⟧
             ; ⟦⟧-cong       to U⟦⟧-cong
             )

  open _→ₕ_ H
  open _→ₕ_ G renaming (h to g; h-cong to g-cong; h-hom to g-hom)

  open import Data.Vec using (map)
  open import Data.Vec.Properties using (map-∘)
  open import Data.Vec.Relation.Binary.Equality.Setoid Cₛ
  open import Relation.Binary using (IsEquivalence)
  open import Relation.Binary.Reasoning.Setoid Cₛ
  open import Function using (_∘_; _$_)
  open import Function.Construct.Composition using (congruent)

  ∘ₕ-cong : Congruent _≈ₛ_ _≈ᵤ_ (h ∘ g)
  ∘ₕ-cong = congruent _≈ₛ_ _≈ₜ_ _≈ᵤ_ g-cong h-cong

  ∘ₕ-hom : Homomorphic S U (h ∘ g)
  ∘ₕ-hom {n} f xs = begin
      U⟦ f ⟧ (map (h ∘ g) xs)
    ≈⟨ U⟦⟧-cong f $ IsEquivalence.reflexive (≋-isEquivalence n) (map-∘ h g xs) ⟩
      U⟦ f ⟧ (map h (map g xs))
    ≈⟨ h-hom f (map g xs) ⟩
      h (T⟦ f ⟧ (map g xs))
    ≈⟨ h-cong (g-hom f xs) ⟩
      h (g (S⟦ f ⟧ xs))
    ∎

  infixr 9 _∘ₕ_

  _∘ₕ_ : (S →ₕ U)
  _∘ₕ_ = record { h      = h ∘ g
                ; h-cong = ∘ₕ-cong
                ; h-hom  = ∘ₕ-hom
                }
