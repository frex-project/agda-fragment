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
    Σ   : Signature
    eqs : (arity : ℕ) → List (Eq Σ arity)

  open Signature Σ

open Theory public

{-
module _ (Σ : Signature) (e : ops Σ 0) where

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ 1 ⦊)

  u : ops (Σ ⦉ 1 ⦊) 0
  u = (inj₁ e)

  a₁ : ops (Σ ⦉ 1 ⦊) 0
  a₁ = (inj₂ (# 0))

  idₗ : ops Σ 2 → Eq Σ 1
  idₗ f = (u ₀) < f >₂ (a₁ ₀) , (a₁ ₀)
  
  idᵣ : ops Σ 2 → Eq Σ 1
  idᵣ f = (a₁ ₀) < f >₂ (u ₀) , (a₁ ₀)

module _ (Σ : Signature) (f : ops Σ 2) where

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ 3 ⦊)

  a₃ : ops (Σ ⦉ 3 ⦊) 0
  a₃ = (inj₂ (# 0))

  b₃ : ops (Σ ⦉ 3 ⦊) 0
  b₃ = (inj₂ (# 1))

  c₃ : ops (Σ ⦉ 3 ⦊) 0
  c₃ = (inj₂ (# 2))

  assoc₂ : Eq Σ 3
  assoc₂ =
      ((a₃ ₀) < f >₂ (b₃ ₀)) < f >₂ (c₃ ₀)
    ,
      (a₃ ₀) < f >₂ ((b₃ ₀) < f >₂ (c₃ ₀))

monoid-eqs : (n : ℕ) → List (Eq monoid-sig n)
monoid-eqs 1 = (idₗ monoid-sig e •) ∷ (idᵣ monoid-sig e •) ∷ []
monoid-eqs 3 = (assoc₂ monoid-sig •) ∷ []
monoid-eqs _ = []

monoid-theory : Theory
monoid-theory = record { Σ   = monoid-sig
                       ; eqs = monoid-eqs
                       }
-}
