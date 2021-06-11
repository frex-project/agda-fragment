{-# OPTIONS --without-K --exact-split --safe #-}

module Fragment.Algebra.Signature where

open import Data.Nat using (ℕ)

record Signature : Set₁ where
  field
    ops : ℕ → Set

open Signature public

data ExtendedOp (Σ : Signature) (O : ℕ → Set) : ℕ → Set where
  newₒ : ∀ {n} → O n → ExtendedOp Σ O n
  oldₒ : ∀ {n} → ops Σ n → ExtendedOp Σ O n

_⦅_⦆ : (Σ : Signature) → (ℕ → Set) → Signature
Σ ⦅ O ⦆ = record { ops = ExtendedOp Σ O }
