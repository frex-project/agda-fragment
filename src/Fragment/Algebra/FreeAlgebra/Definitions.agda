{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.FreeAlgebra.Definitions where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Signature

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

private
  variable
    a ℓ : Level

Environment : {Σ : Signature} → ℕ → Algebra Σ {a} {ℓ} → Set a
Environment n S = Fin n → Algebra.Carrier S
