{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Properties (Σ : Signature) where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Homomorphism.Base Σ

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
  
  open import Fragment.Algebra.Homomorphism.Setoid Σ S T

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

  open import Fragment.Algebra.Homomorphism.Setoid Σ S V

  ∘ₕ-assoc : (H ∘ₕ G) ∘ₕ F ≡ₕ H ∘ₕ (G ∘ₕ F)
  ∘ₕ-assoc {x} = refl
