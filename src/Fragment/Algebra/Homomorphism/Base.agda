{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Base (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism.Definitions Σ

open import Level using (Level; _⊔_)
open import Function using (id; _∘_; _$_)
open import Function.Construct.Composition using (congruent)
open import Relation.Binary using (IsEquivalence)
open import Data.Vec using (map)
open import Data.Vec.Properties using (map-id; map-∘)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  (S : Algebra {a} {ℓ₁})
  (T : Algebra {b} {ℓ₂})
  where

  infixr 1 _→ₕ_

  record _→ₕ_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ∥_∥ₕ      : ∥ S ∥ → ∥ T ∥
      ∥_∥ₕ-cong : Congruent ≈[ S ] ≈[ T ] ∥_∥ₕ
      ∥_∥ₕ-hom  : Homomorphic S T ∥_∥ₕ

open _→ₕ_ public

module _ (S : Algebra {a} {ℓ₁}) where

  open import Data.Vec.Relation.Binary.Equality.Setoid ∥ S ∥/≈

  id-cong : Congruent ≈[ S ] ≈[ S ] id
  id-cong x≈y = x≈y

  id-hom : Homomorphic S S id
  id-hom {n} f xs = (S ⟦⟧-cong) f $ reflexive (map-id xs)
    where open IsEquivalence (≋-isEquivalence n) using (reflexive)

  idₕ : S →ₕ S
  idₕ = record { ∥_∥ₕ      = id
               ; ∥_∥ₕ-cong = id-cong
               ; ∥_∥ₕ-hom  = id-hom
               }

module _
  {S : Algebra {a} {ℓ₁}}
  {T : Algebra {b} {ℓ₂}}
  {U : Algebra {c} {ℓ₃}}
  (h : T →ₕ U)
  (g : S →ₕ T)
  where

  open import Data.Vec.Relation.Binary.Equality.Setoid ∥ U ∥/≈
  open import Relation.Binary.Reasoning.Setoid ∥ U ∥/≈

  ∘ₕ-cong : Congruent ≈[ S ] ≈[ U ] (∥ h ∥ₕ ∘ ∥ g ∥ₕ)
  ∘ₕ-cong = congruent ≈[ S ] ≈[ T ] ≈[ U ] ∥ g ∥ₕ-cong ∥ h ∥ₕ-cong

  ∘ₕ-hom : Homomorphic S U (∥ h ∥ₕ ∘ ∥ g ∥ₕ)
  ∘ₕ-hom {n} f xs = begin
      (U ⟦ f ⟧) (map (∥ h ∥ₕ ∘ ∥ g ∥ₕ) xs)
    ≈⟨ (U ⟦⟧-cong) f $ reflexive (map-∘ ∥ h ∥ₕ ∥ g ∥ₕ xs) ⟩
      (U ⟦ f ⟧) (map ∥ h ∥ₕ (map ∥ g ∥ₕ xs))
    ≈⟨ ∥ h ∥ₕ-hom f (map ∥ g ∥ₕ xs) ⟩
      ∥ h ∥ₕ ((T ⟦ f ⟧) (map ∥ g ∥ₕ xs))
    ≈⟨ ∥ h ∥ₕ-cong (∥ g ∥ₕ-hom f xs) ⟩
      ∥ h ∥ₕ (∥ g ∥ₕ (S ⟦ f ⟧ $ xs))
    ∎
    where open IsEquivalence (≋-isEquivalence n) using (reflexive)

  infixr 9 _∘ₕ_

  _∘ₕ_ : (S →ₕ U)
  _∘ₕ_ = record { ∥_∥ₕ      = ∥ h ∥ₕ ∘ ∥ g ∥ₕ
                ; ∥_∥ₕ-cong = ∘ₕ-cong
                ; ∥_∥ₕ-hom  = ∘ₕ-hom
                }
