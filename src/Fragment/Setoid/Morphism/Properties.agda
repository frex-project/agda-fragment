{-# OPTIONS --without-K --exact-split --safe #-}

module Fragment.Setoid.Morphism.Properties where

open import Fragment.Setoid.Morphism.Base
open import Fragment.Setoid.Morphism.Setoid

open import Level using (Level)
open import Relation.Binary using (Setoid)

private
  variable
    a b c d ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Setoid a ℓ₁
    B : Setoid b ℓ₂
    C : Setoid c ℓ₃
    D : Setoid d ℓ₄

id-unitˡ : ∀ {f : A ↝ B} → id · f ≗ f
id-unitˡ {B = B} = Setoid.refl B

id-unitʳ : ∀ {f : A ↝ B} → f · id ≗ f
id-unitʳ {B = B} = Setoid.refl B

·-assoc : ∀ (h : C ↝ D) (g : B ↝ C) (f : A ↝ B)
          → (h · g) · f ≗ h · (g · f)
·-assoc {D = D} _ _ _ = Setoid.refl D

·-congˡ : ∀ (h : B ↝ C) (f g : A ↝ B)
          → f ≗ g
          → h · f ≗ h · g
·-congˡ h _ _ f≗g = ∣ h ∣-cong f≗g

·-congʳ : ∀ (h : A ↝ B) (f g : B ↝ C)
          → f ≗ g
          → f · h ≗ g · h
·-congʳ _ _ _ f≗g = f≗g
