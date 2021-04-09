{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.Signature where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_)

record Signature : Set₁ where
  field
    ops : ℕ → Set

open Signature public

_⦉_⦊ : (Σ : Signature) → ℕ → Signature
Σ ⦉ n ⦊ = record { ops = extend Σ n }
  where extend : Signature → ℕ → ℕ → Set
        extend Σ n 0 = (ops Σ 0) ⊎ Fin n
        extend Σ _ n = ops Σ n
