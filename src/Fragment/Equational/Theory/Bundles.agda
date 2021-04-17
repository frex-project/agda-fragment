{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory.Bundles where

{-
open import Fragment.Algebra.Signature
open import Fragment.Equational.Theory.Base
open import Fragment.Equational.Theory.Combinators

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)

open import Relation.Nullary using (yes ; no)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

module _ where

  data MagmaOp : ℕ → Set where
    • : MagmaOp 2

  Σ-magma : Signature
  Σ-magma = record { ops = MagmaOp
                   ; _≟_ = λ {k} → _≟_ {k}
                   }
    where _≟_ : ∀ {k} → Decidable {A = MagmaOp k} _≡_
          • ≟ • = yes (PE.refl)

  import Fragment.Equational.Theory.Laws Σ-magma as L

  data MagmaEq : ℕ → Set where

  magma-eqs : ∀ {n} → MagmaEq n → Eq Σ-magma n
  magma-eqs ()

  data SemigroupEq : ℕ → Set where
    assoc : SemigroupEq 3

  semigroup-eqs : ∀ {n} → SemigroupEq n → Eq Σ-magma n
  semigroup-eqs assoc = L.assoc •

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

Θ-monoid : Theory
Θ-monoid = AddId Θ-semigroup •
-}
