{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Signature
  renaming (_⦉_⦊ to _⦉_⦊ₛ)

import Fragment.Algebra.TermAlgebra as T

open import Function using (_∘_)

open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Bool using (true; false)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)

Eq : (Σ : Signature) → (n : ℕ) → Set
Eq Σ n = Expr × Expr
  where open T (Σ ⦉ n ⦊ₛ)

record Theory : Set₁ where
  field
    Σ     : Signature
    eqs   : ℕ → Set
    _⟦_⟧ₑ : ∀ {arity : ℕ} → (eqs arity) → Eq Σ arity

  open Signature Σ

open Theory public

mutual
    frex-expr-args : ∀ {Σ n m arity}
                     → Vec (T.Expr (Σ ⦉ m ⦊ₛ)) arity
                     → Vec (T.Expr ((Σ ⦉ n ⦊ₛ) ⦉ m ⦊ₛ)) arity
    frex-expr-args []       = []
    frex-expr-args (x ∷ xs) = (frex-expr x) ∷ (frex-expr-args xs)

    frex-expr : ∀ {Σ n m}
                → T.Expr (Σ ⦉ m ⦊ₛ)
                → T.Expr ((Σ ⦉ n ⦊ₛ) ⦉ m ⦊ₛ)
    frex-expr (T.term (inj₂ k) []) = T.term (inj₂ k) []
    frex-expr (T.term (inj₁ f) []) = T.term (inj₁ (inj₁ f)) []
    frex-expr (T.term f (x ∷ xs))  = T.term f (frex-expr-args (x ∷ xs))

frex-eq : ∀ {Σ n arity}
          → Eq Σ arity
          → Eq (Σ ⦉ n ⦊ₛ) arity
frex-eq (lhs , rhs) = frex-expr lhs , frex-expr rhs

_⦉_⦊ : (Θ : Theory) → ℕ → Theory
Θ ⦉ n ⦊ = record { Σ     = (Σ Θ) ⦉ n ⦊ₛ
                 ; eqs   = eqs Θ
                 ; _⟦_⟧ₑ = frex-eq ∘ (Θ ⟦_⟧ₑ)
                 }

{-
_∥_∥-eqs : (Σ : Signature) → (n : ℕ) → ℕ → Set
_∥_∥-eqs Σ n m with n ≡ᵇ m
...              | true  = ⊤
...              | false = ⊥

_∥_∥ : (Σ : Signature) → {n : ℕ} → Eq Σ n → Theory
_∥_∥ Σ {n = n} eq = record { Σ     = Σ
                          ; eqs   = Σ ∥ n ∥-eqs
                          ; _⟦_⟧ₑ = {!!}
                          }
-}
