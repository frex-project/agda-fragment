{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.TermModel.Base (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra (Σ Θ)
open import Fragment.Algebra.Quotient (Σ Θ)
open import Fragment.Algebra.TermAlgebra (Σ Θ)
open import Fragment.Algebra.FreeAlgebra (Σ Θ)

open import Fragment.Equational.Model Θ
open import Fragment.Equational.Initial Θ
open import Fragment.Equational.TermModel.ProvableEquivalence Θ |T|

open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Data.Product using (proj₁; proj₂)

Herbrand/≈ₘ : Setoid _ _
Herbrand/≈ₘ = record { Carrier       = Expr
                     ; _≈_           = _≈ₘ_
                     ; isEquivalence = ≈ₘ-isEquivalence
                     }

|T|/≈ₘ : Algebra
|T|/≈ₘ = |T| / ≈ₘ

open import Relation.Binary.Reasoning.Setoid Herbrand/≈ₘ

|T|/≈ₘ-models : Models |T|/≈ₘ
|T|/≈ₘ-models eq {θ} = begin
    subst |T|/≈ₘ θ lhs
  ≈⟨ reflexive (quotient-subst lhs) ⟩
    subst |T| θ lhs
  ≈⟨ model eq θ ⟩
    subst |T| θ rhs
  ≈⟨ reflexive (quotient-subst rhs) ⟩
    subst |T|/≈ₘ θ rhs
  ∎
  where open IsEquivalence ≈ₘ-isEquivalence
        lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
        rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

|T|/≈ₘ-isModel : IsModel Herbrand/≈ₘ
|T|/≈ₘ-isModel = record { isAlgebra = |T| / ≈ₘ -isAlgebra
                        ; models    = |T|/≈ₘ-models
                        }

|T|ₘ : Model
|T|ₘ = record { ∥_∥/≈    = Herbrand/≈ₘ
              ; isModel  = |T|/≈ₘ-isModel
              }
