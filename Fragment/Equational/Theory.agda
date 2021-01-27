{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory where

open import Fragment.Algebra.Signature

import Fragment.Algebra.TermAlgebra as T

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (_×_)

Eq : (Σ : Signature) → (n : ℕ) → Set
Eq Σ n = Expr × Expr
  where open T (Σ ⦉ n ⦊)

record Theory : Set₁ where
  field
    Σ     : Signature
    eqs   : ℕ → Set
    _⟦_⟧ₑ : ∀ {arity : ℕ} → (eqs arity) → Eq Σ arity

  open Signature Σ

open Theory public
