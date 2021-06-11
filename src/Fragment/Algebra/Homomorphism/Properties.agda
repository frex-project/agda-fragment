{-# OPTIONS --without-K --exact-split --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Properties (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism.Base Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ

open import Level using (Level)
open import Relation.Binary using (Setoid)

private
  variable
    a b c d ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Algebra {a} {ℓ₁}
    B : Algebra {b} {ℓ₂}
    C : Algebra {c} {ℓ₃}
    D : Algebra {d} {ℓ₄}

id-unitˡ : ∀ {f : A ⟿ B} → id ⊙ f ≗ f
id-unitˡ {B = B} = Setoid.refl ∥ B ∥/≈

id-unitʳ : ∀ {f : A ⟿ B} → f ⊙ id ≗ f
id-unitʳ {B = B} = Setoid.refl ∥ B ∥/≈

⊙-assoc : ∀ (h : C ⟿ D) (g : B ⟿ C) (f : A ⟿ B)
          → (h ⊙ g) ⊙ f ≗ h ⊙ (g ⊙ f)
⊙-assoc {D = D} _ _ _ = Setoid.refl ∥ D ∥/≈

⊙-congˡ : ∀ (h : B ⟿ C) (f g : A ⟿ B)
          → f ≗ g
          → h ⊙ f ≗ h ⊙ g
⊙-congˡ h _ _ f≗g = ∣ h ∣-cong f≗g

⊙-congʳ : ∀ (h : A ⟿ B) (f g : B ⟿ C)
          → f ≗ g
          → f ⊙ h ≗ g ⊙ h
⊙-congʳ _ _ _ f≗g = f≗g
