{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Properties (Σ : Signature) where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Homomorphism.Base Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ

open import Level using (Level)

private
  variable
    a b c d ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  (H : S →ₕ T)
  where

  open Algebra T

  idₕ-unitˡ : idₕ T ∘ₕ H ≡ₕ H
  idₕ-unitˡ {x} = refl

  idₕ-unitʳ : H ∘ₕ idₕ S ≡ₕ H
  idₕ-unitʳ {x} = refl

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  {U : Algebra Σ {c} {ℓ₃}}
  {V : Algebra Σ {d} {ℓ₄}}
  (H : U →ₕ V)
  (G : T →ₕ U)
  (F : S →ₕ T)
  where

  open Algebra V

  ∘ₕ-assoc : (H ∘ₕ G) ∘ₕ F ≡ₕ H ∘ₕ (G ∘ₕ F)
  ∘ₕ-assoc {x} = refl

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  (H : S →ₕ T)
  where

  ∘ₕ-congˡ : ∀ {R : Algebra Σ {c} {ℓ₃}}
             → (F : R →ₕ S)
             → (G : R →ₕ S)
             → F ≡ₕ G → H ∘ₕ F ≡ₕ H ∘ₕ G
  ∘ₕ-congˡ _ _ F≡ₕG {x} = h-cong (F≡ₕG {x})
    where open _→ₕ_ H

  ∘ₕ-congʳ : ∀ {U : Algebra Σ {c} {ℓ₃}}
             → (F : T →ₕ U)
             → (G : T →ₕ U)
             → F ≡ₕ G → F ∘ₕ H ≡ₕ G ∘ₕ H
  ∘ₕ-congʳ _ _ F≡ₕG {x} = F≡ₕG {h x}
    where open _→ₕ_ H
