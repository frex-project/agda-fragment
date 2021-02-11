{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.TermModel.Base (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra (Σ Θ)
open import Fragment.Algebra.Quotient
open import Fragment.Algebra.TermAlgebra (Σ Θ)
open import Fragment.Algebra.FreeAlgebra

open import Fragment.Equational.Model
open import Fragment.Equational.Initial Θ
open import Fragment.Equational.TermModel.ProvableEquivalence Θ |T|

open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)

Herbrandₘ : Setoid _ _
Herbrandₘ = record { Carrier       = Expr
                   ; _≈_           = _≈ₘ_
                   ; isEquivalence = ≈ₘ-isEquivalence
                   }

≡⊂≈ₘ : underlyingEquivalence |T| ⊂ ≈ₘ
≡⊂≈ₘ x≡y = (IsEquivalence.reflexive ≈ₘ-isEquivalence) x≡y

|T|/≈ₘ : Algebra
|T|/≈ₘ = |T| / ≈ₘ

open import Relation.Binary.Reasoning.Setoid Herbrandₘ

|T|/≈ₘ-models : Models Θ |T|/≈ₘ
|T|/≈ₘ-models eq {θ} = begin
    subst |T|/≈ₘ θ lhs
  ≈⟨ IsEquivalence.reflexive ≈ₘ-isEquivalence (quotient-subst lhs) ⟩
    subst |T| θ lhs
  ≈⟨ model eq θ ⟩
    subst |T| θ rhs
  ≈⟨ IsEquivalence.reflexive ≈ₘ-isEquivalence (quotient-subst rhs) ⟩
    subst |T|/≈ₘ θ rhs
  ∎
  where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
        rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

|T|/≈ₘ-isModel : IsModel Θ Herbrandₘ
|T|/≈ₘ-isModel = record { isAlgebra = |T| / ≈ₘ -isAlgebra
                        ; models    = |T|/≈ₘ-models
                        }

|T|ₘ : Model Θ
|T|ₘ = record { Carrierₛ = Herbrandₘ
              ; isModel  = |T|/≈ₘ-isModel
              }
