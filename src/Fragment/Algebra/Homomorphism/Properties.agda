{-# OPTIONS --without-K --safe #-}

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
    S : Algebra {a} {ℓ₁}
    T : Algebra {b} {ℓ₂}
    U : Algebra {c} {ℓ₃}
    V : Algebra {d} {ℓ₄}

idₕ-unitˡ : ∀ (h : S →ₕ T) → idₕ T ∘ₕ h ≡ₕ h
idₕ-unitˡ {T = T} _ {x} = Setoid.refl ∥ T ∥/≈

idₕ-unitʳ : ∀ (h : S →ₕ T) → h ∘ₕ idₕ S ≡ₕ h
idₕ-unitʳ {T = T} _ {x} = Setoid.refl ∥ T ∥/≈

∘ₕ-assoc : ∀ (h : U →ₕ V) (g : T →ₕ U) (f : S →ₕ T)
           → (h ∘ₕ g) ∘ₕ f ≡ₕ h ∘ₕ (g ∘ₕ f)
∘ₕ-assoc {V = V} _ _ _ {x} = Setoid.refl ∥ V ∥/≈

∘ₕ-congˡ : ∀ (h : S →ₕ T)
           → (f : U →ₕ S) → (g : U →ₕ S)
           → f ≡ₕ g → h ∘ₕ f ≡ₕ h ∘ₕ g
∘ₕ-congˡ h _ _ f≡ₕh {x} = ∥ h ∥ₕ-cong (f≡ₕh {x})

∘ₕ-congʳ : ∀ (h : S →ₕ T)
           → (f : T →ₕ U) → (g : T →ₕ U)
           → f ≡ₕ g → f ∘ₕ h ≡ₕ g ∘ₕ h
∘ₕ-congʳ h _ _ f≡ₕg {x} = f≡ₕg {∥ h ∥ₕ x}
