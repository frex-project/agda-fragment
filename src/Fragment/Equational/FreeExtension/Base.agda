{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension.Base (Θ : Theory) where

{-
open import Fragment.Equational.Model Θ
open import Fragment.Equational.Coproduct Θ

open import Level using (Level; Setω; _⊔_)
open import Data.Nat using (ℕ)

private
  variable
    a ℓ : Level

Extension : Setω
Extension = ∀ {a} {ℓ} → Model {a} {ℓ} → ℕ → Model {a} {a ⊔ ℓ}

IsFreeExtension : Extension → Setω
IsFreeExtension _[_] =
  ∀ {a ℓ} (A : Model {a} {ℓ}) (n : ℕ) → IsCoproduct A (J n) (A [ n ])

record FreeExtension : Setω where
  field
    _[_]        : Extension
    _[_]-isFrex : IsFreeExtension _[_]
-}
