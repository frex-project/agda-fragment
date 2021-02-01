{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.TermModel (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Quotient
open import Fragment.Algebra.TermAlgebra (Σ Θ)
open import Fragment.Algebra.FreeAlgebra

open import Fragment.Equational.Model

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)

data _≈ₘ_ : Expr → Expr → Set where
  refl  : ∀ {x} → x ≈ₘ x
  sym   : ∀ {x y} → x ≈ₘ y → y ≈ₘ x
  trans : ∀ {x y z} → x ≈ₘ y → y ≈ₘ z → x ≈ₘ z
  cong  : ∀ {arity} → (f : ops (Σ Θ) arity)
          → ∀ {xs ys} → Pointwise _≈ₘ_ xs ys
          → term f xs ≈ₘ term f ys
  model : ∀ {n} → (eq : eqs Θ n) → (θ : Environment n |T|)
          → subst |T| θ (proj₁ (Θ ⟦ eq ⟧ₑ)) ≈ₘ subst |T| θ (proj₂ (Θ ⟦ eq ⟧ₑ))

≈ₘ-isEquivalence : IsEquivalence _≈ₘ_
≈ₘ-isEquivalence = record { refl  = refl
                          ; sym   = sym
                          ; trans = trans
                          }

Herbrandₘ : Setoid _ _
Herbrandₘ = record { Carrier       = Expr
                   ; _≈_           = _≈ₘ_
                   ; isEquivalence = ≈ₘ-isEquivalence
                   }

≈ₘ-cong : Congruence (Σ Θ) Herbrandₘ term
≈ₘ-cong = cong

≈ₘ : CompatibleEquivalence |T|
≈ₘ = record { _▲_           = _≈ₘ_
            ; isEquivalence = ≈ₘ-isEquivalence
            ; compatible    = ≈ₘ-cong
            }

|T|ₘ : Algebra (Σ Θ)
|T|ₘ = |T| / ≈ₘ

-- |T|ₘ-models : Models Θ |T|ₘ
-- |T|ₘ-models eq {θ} = model eq θ
