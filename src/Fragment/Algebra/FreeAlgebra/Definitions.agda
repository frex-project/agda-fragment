{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.FreeAlgebra.Definitions (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

Environment : ∀ {a ℓ} → ℕ → Algebra {a} {ℓ} → Set a
Environment n S = Fin n → ∥ S ∥
