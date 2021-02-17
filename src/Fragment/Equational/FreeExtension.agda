{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension (Θ : Theory) where

open import Fragment.Equational.Model
open import Fragment.Equational.FreeModel
open import Fragment.Equational.Coproduct Θ

open import Fragment.Algebra.FreeAlgebra using (Environment)
open import Fragment.Algebra.Homomorphism (Σ Θ)

open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Level using (Level; Setω)

private
  variable
    a b ℓ₁ ℓ₂ : Level

IsFreeExtension : Model Θ {a} {ℓ₁} → ℕ → Model Θ {b} {ℓ₂} → Setω
IsFreeExtension M n N = IsCoproduct M (|T|ₘ Θ ⦉ n ⦊) N

module _
  {M : Model Θ {a} {ℓ₁}}
  {F : Model Θ {b} {ℓ₂}}
  {n : ℕ}
  (F-frex : IsFreeExtension M n F)
  where

  open Model M renaming (Carrierₐ to S; Carrier to A)
  open Model F renaming (_≈_ to _≈ₓ_; Carrierₐ to FXₐ; Carrier to FX)
  open IsCoproduct F-frex

  reduceₕ : (θ : Environment n S) → FXₐ →ₕ S
  reduceₕ θ = ([_,_] {W = M} (idₕ S) (substₕ M θ))

  reduce : (θ : Environment n S) → FX → A
  reduce θ x = applyₕ (reduceₕ θ) x

  fundamental : ∀ {x y : FX}
                → x ≈ₓ y
                → (θ : Environment n S)
                → reduce θ x ≈ reduce θ y
  fundamental x≈ₓy θ = _→ₕ_.h-cong (reduceₕ θ) x≈ₓy
