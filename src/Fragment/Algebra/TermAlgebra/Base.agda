{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.TermAlgebra.Base (Σ : Signature) where

open import Fragment.Algebra.Algebra

import Relation.Binary.PropositionalEquality as PE
open import Data.Vec using (Vec)
open import Relation.Binary using (Setoid)
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)

data Expr : Set where
  term : ∀ {arity} → (f : ops Σ arity) → Vec Expr arity → Expr

Herbrand : Setoid _ _
Herbrand = PE.setoid Expr

term-cong : Congruence Σ Herbrand term
term-cong f p = PE.cong (term f) (≋⇒≡ p)

|T|-isAlgebra : IsAlgebra Σ Herbrand
|T|-isAlgebra = record { ⟦_⟧     = term
                       ; ⟦⟧-cong = term-cong
                       }

|T| : Algebra Σ
|T| = record { Carrierₛ  = Herbrand
             ; isAlgebra = |T|-isAlgebra
             }
