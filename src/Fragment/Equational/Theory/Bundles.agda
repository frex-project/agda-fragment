{-# OPTIONS --without-K --exact-split --safe #-}

module Fragment.Equational.Theory.Bundles where

open import Fragment.Algebra.Signature
open import Fragment.Equational.Theory.Base
open import Fragment.Equational.Theory.Combinators

open import Data.Nat using (ℕ)

module _ where

  data MagmaOp : ℕ → Set where
    • : MagmaOp 2

  Σ-magma : Signature
  Σ-magma = record { ops = MagmaOp }

  import Fragment.Equational.Theory.Laws Σ-magma as L

  data MagmaEq : ℕ → Set where

  magma-eqs : ∀ {n} → MagmaEq n → Eq Σ-magma n
  magma-eqs ()

  data SemigroupEq : ℕ → Set where
    assoc : SemigroupEq 3

  semigroup-eqs : ∀ {n} → SemigroupEq n → Eq Σ-magma n
  semigroup-eqs assoc = L.assoc •

  data CSemigroupEq : ℕ → Set where
    comm  : CSemigroupEq 2
    assoc : CSemigroupEq 3

  csemigroup-eqs : ∀ {n} → CSemigroupEq n → Eq Σ-magma n
  csemigroup-eqs comm  = L.comm •
  csemigroup-eqs assoc = L.assoc •

Θ-magma : Theory
Θ-magma = record { Σ     = Σ-magma
                 ; eqs   = MagmaEq
                 ; _⟦_⟧ₑ = magma-eqs
                 }

Θ-semigroup : Theory
Θ-semigroup = record { Σ     = Σ-magma
                     ; eqs   = SemigroupEq
                     ; _⟦_⟧ₑ = semigroup-eqs
                     }

Θ-csemigroup : Theory
Θ-csemigroup = record { Σ     = Σ-magma
                      ; eqs   = CSemigroupEq
                      ; _⟦_⟧ₑ = csemigroup-eqs
                      }

Θ-monoid : Theory
Θ-monoid = AddId Θ-semigroup •

Θ-cmonoid : Theory
Θ-cmonoid = AddId Θ-csemigroup •
