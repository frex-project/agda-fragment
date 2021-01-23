{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.Signature where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_)

record Signature : Set₁ where
  field
    ops : ℕ → Set

frex : (ℕ → Set) → ℕ → ℕ → Set
frex ops n 0 = ops 0 ⊎ Fin n
frex ops _ n = ops n

_⦉_⦊ : (Σ : Signature) → ℕ → Signature
Σ ⦉ n ⦊ = record { ops = frex ops n }
  where open Signature Σ

open Signature public

data MonoidOp : ℕ → Set where
  e : MonoidOp 0
  • : MonoidOp 2

monoid-sig : Signature
monoid-sig = record { ops = MonoidOp }
