{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory.Base where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Free
open import Fragment.Algebra.Algebra

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)

Eq : (Σ : Signature) → (n : ℕ) → Set
Eq Σ n = ∥ F Σ n ∥ × ∥ F Σ n ∥

record Theory : Set₁ where
  field
    Σ     : Signature
    eqs   : ℕ → Set
    _⟦_⟧ₑ : ∀ {arity : ℕ} → (eqs arity) → Eq Σ arity

  open Signature Σ

open Theory public
