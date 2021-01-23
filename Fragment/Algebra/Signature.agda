{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.Signature where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_)

record Signature : Set₁ where
  field
    ops : ℕ → Set

open Signature public

frex : Signature → ℕ → ℕ → Set
frex Σ n 0 = (ops Σ 0) ⊎ Fin n
frex Σ _ n = ops Σ n

_⦉_⦊ : (Σ : Signature) → ℕ → Signature
Σ ⦉ n ⦊ = record { ops = frex Σ n }


{-
data MonoidOp : ℕ → Set where
  e : MonoidOp 0
  • : MonoidOp 2

monoid-sig : Signature
monoid-sig = record { ops = MonoidOp }
-}
