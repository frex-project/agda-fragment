{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Bundles where

open import Fragment.Algebra.Signature
open import Fragment.Equational.Theory

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)

module _ where

  private

    data MagmaOp : ℕ → Set where
      • : MagmaOp 2

  Σ-magma : Signature
  Σ-magma = record { ops = MagmaOp }

  open import Fragment.Equational.Laws Σ-magma

  magma-eqs : (arity : ℕ) → List (Eq Σ-magma arity)
  magma-eqs _ = []

  semigroup-eqs : (arity : ℕ) → List (Eq Σ-magma arity)
  semigroup-eqs 3 = (assoc •) ∷ magma-eqs 3
  semigroup-eqs n = magma-eqs n

  csemigroup-eqs : (arity : ℕ) → List (Eq Σ-magma arity)
  csemigroup-eqs 2 = (comm •) ∷ semigroup-eqs 2
  csemigroup-eqs n = semigroup-eqs n

module _ where

  private

    data MonoidOp : ℕ → Set where
      e : MonoidOp 0
      • : MonoidOp 2

  Σ-monoid : Signature
  Σ-monoid = record { ops = MonoidOp }

  open import Fragment.Equational.Laws Σ-monoid

  monoid-eqs : (arity : ℕ) → List (Eq Σ-monoid arity)
  monoid-eqs 1 = (idₗ e •) ∷ (idᵣ e •) ∷ []
  monoid-eqs 3 = (assoc •) ∷ []
  monoid-eqs _ = []

  cmonoid-eqs : (arity : ℕ) → List (Eq Σ-monoid arity)
  cmonoid-eqs 2 = (comm •) ∷ monoid-eqs 2
  cmonoid-eqs n = monoid-eqs n

module _ where

  private

    data GroupOp : ℕ → Set where
      e : GroupOp 0
      ~ : GroupOp 1
      • : GroupOp 2

  Σ-group : Signature
  Σ-group = record { ops = GroupOp }

  open import Fragment.Equational.Laws Σ-group

  group-eqs : (arity : ℕ) → List (Eq Σ-group arity)
  group-eqs 1 = (idₗ e •) ∷ (idᵣ e •) ∷ (invₗ e ~ •) ∷ (invᵣ e ~ •) ∷ []
  group-eqs 3 = (assoc •) ∷ []
  group-eqs _ = []

  abelian-group-eqs : (arity : ℕ) → List (Eq Σ-group arity)
  abelian-group-eqs 2 = (comm •) ∷ group-eqs 2
  abelian-group-eqs n = group-eqs n

Θ-magma : Theory
Θ-magma = record { Σ   = Σ-magma
                 ; eqs = magma-eqs
                 }

Θ-semigroup : Theory
Θ-semigroup = record { Σ   = Σ-magma
                     ; eqs = semigroup-eqs
                     }

Θ-csemigroup : Theory
Θ-csemigroup = record { Σ   = Σ-magma
                      ; eqs = csemigroup-eqs
                      }

Θ-monoid : Theory
Θ-monoid = record { Σ   = Σ-monoid
                  ; eqs = monoid-eqs
                  }

Θ-cmonoid : Theory
Θ-cmonoid = record { Σ   = Σ-monoid
                   ; eqs = cmonoid-eqs
                   }

Θ-group : Theory
Θ-group = record { Σ   = Σ-group
                 ; eqs = group-eqs
                 }

Θ-abelian-group : Theory
Θ-abelian-group = record { Σ   = Σ-group
                         ; eqs = abelian-group-eqs
                         }
