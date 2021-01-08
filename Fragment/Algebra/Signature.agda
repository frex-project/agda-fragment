{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.Signature where

open import Data.Nat using (ℕ)

record Signature : Set₁ where
  field
    ops : ℕ → Set

open Signature public

data MonoidOp : ℕ → Set where
  e : MonoidOp 0
  • : MonoidOp 2

monoid-sig : Signature
monoid-sig = record { ops = MonoidOp }
