{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory.Bundles where

open import Fragment.Algebra.Signature
open import Fragment.Equational.Theory.Base

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)

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

module _ where

  data MonoidOp : ℕ → Set where
    e : MonoidOp 0
    • : MonoidOp 2

  Σ-monoid : Signature
  Σ-monoid = record { ops = MonoidOp }

  import Fragment.Equational.Theory.Laws Σ-monoid as L

  data MonoidEq : ℕ → Set where
    idₗ   : MonoidEq 1
    idᵣ   : MonoidEq 1
    assoc : MonoidEq 3

  monoid-eqs : ∀ {n} → MonoidEq n → Eq Σ-monoid n
  monoid-eqs idₗ   = L.idₗ e •
  monoid-eqs idᵣ   = L.idᵣ e •
  monoid-eqs assoc = L.assoc •

  data CMonoidEq : ℕ → Set where
    idₗ   : CMonoidEq 1
    idᵣ   : CMonoidEq 1
    comm  : CMonoidEq 2
    assoc : CMonoidEq 3

  cmonoid-eqs : ∀ {n} → CMonoidEq n → Eq Σ-monoid n
  cmonoid-eqs idₗ   = L.idₗ e •
  cmonoid-eqs idᵣ   = L.idᵣ e •
  cmonoid-eqs comm  = L.comm •
  cmonoid-eqs assoc = L.assoc •

module _ where

  data GroupOp : ℕ → Set where
    e : GroupOp 0
    ~ : GroupOp 1
    • : GroupOp 2

  Σ-group : Signature
  Σ-group = record { ops = GroupOp }

  import Fragment.Equational.Theory.Laws Σ-group as L

  data GroupEq : ℕ → Set where
    idₗ   : GroupEq 1
    idᵣ   : GroupEq 1
    invₗ  : GroupEq 1
    invᵣ  : GroupEq 1
    assoc : GroupEq 3

  group-eqs : ∀ {n} → GroupEq n → Eq Σ-group n
  group-eqs idₗ   = L.idₗ e •
  group-eqs idᵣ   = L.idᵣ e •
  group-eqs invₗ  = L.invₗ e ~ •
  group-eqs invᵣ  = L.invᵣ e ~ •
  group-eqs assoc = L.assoc •

  data AbelianGroupEq : ℕ → Set where
    idₗ   : AbelianGroupEq 1
    idᵣ   : AbelianGroupEq 1
    invₗ  : AbelianGroupEq 1
    invᵣ  : AbelianGroupEq 1
    comm  : AbelianGroupEq 2
    assoc : AbelianGroupEq 3

  abelian-group-eqs : ∀ {n} → AbelianGroupEq n → Eq Σ-group n
  abelian-group-eqs idₗ   = L.idₗ e •
  abelian-group-eqs idᵣ   = L.idᵣ e •
  abelian-group-eqs invₗ  = L.invₗ e ~ •
  abelian-group-eqs invᵣ  = L.invᵣ e ~ •
  abelian-group-eqs comm  = L.comm •
  abelian-group-eqs assoc = L.assoc •

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
Θ-monoid = record { Σ     = Σ-monoid
                  ; eqs   = MonoidEq
                  ; _⟦_⟧ₑ = monoid-eqs
                  }

Θ-cmonoid : Theory
Θ-cmonoid = record { Σ     = Σ-monoid
                   ; eqs   = CMonoidEq
                   ; _⟦_⟧ₑ = cmonoid-eqs
                   }

Θ-group : Theory
Θ-group = record { Σ     = Σ-group
                 ; eqs   = GroupEq
                 ; _⟦_⟧ₑ = group-eqs
                 }

Θ-abelian-group : Theory
Θ-abelian-group = record { Σ     = Σ-group
                         ; eqs   = AbelianGroupEq
                         ; _⟦_⟧ₑ = abelian-group-eqs
                         }
