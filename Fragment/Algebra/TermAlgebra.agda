{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.TermAlgebra (Σ : Signature) where

open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; setoid)

open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)

open Signature

data Expr : Set where
  term : ∀ {arity} → (f : ops Σ arity) → Vec Expr arity → Expr

_₀ : ops Σ 0 → Expr
_₀ f = term f []

<_>₁_ : ops Σ 1 → Expr → Expr
<_>₁_ f t = term f (t ∷ [])

_<_>₂_ : Expr → ops Σ 2 → Expr → Expr
_<_>₂_ s f t = term f (s ∷ t ∷ [])

Herbrand : Setoid _ _
Herbrand = setoid Expr

open import Fragment.Algebra.Algebra Herbrand
  using (Congruence; IsAlgebra)

term-cong : Congruence Σ term
term-cong f xs ys p = cong (term f) (≋⇒≡ p)

|T| : IsAlgebra Σ
|T| = record { ⟦_⟧     = term
             ; ⟦⟧-cong = term-cong
             }
