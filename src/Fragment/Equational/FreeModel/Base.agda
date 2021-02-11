{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory
open import Data.Nat using (ℕ)

module Fragment.Equational.FreeModel.Base
  (Θ : Theory)
  (n : ℕ)
  where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Quotient
open import Fragment.Algebra.FreeAlgebra

open import Fragment.Equational.Model
open import Fragment.Equational.TermModel (Θ ⦉ n ⦊)

open import Data.Sum using (inj₁)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.Reasoning.Setoid Herbrandₘ

|T|_⦉_⦊/≈ₘ-⟦⟧-cong : Congruence (Σ Θ) Herbrandₘ (|T| (Σ Θ) ⦉ n ⦊-⟦_⟧)
|T|_⦉_⦊/≈ₘ-⟦⟧-cong f []       = cong (inj₁ f) []
|T|_⦉_⦊/≈ₘ-⟦⟧-cong f (p ∷ ps) = cong f (p ∷ ps)

|T|_⦉_⦊/≈ₘ-isAlgebra : IsAlgebra (Σ Θ) Herbrandₘ
|T|_⦉_⦊/≈ₘ-isAlgebra = record { ⟦_⟧     = |T| (Σ Θ) ⦉ n ⦊-⟦_⟧
                              ; ⟦⟧-cong = |T|_⦉_⦊/≈ₘ-⟦⟧-cong
                              }
|T|_⦉_⦊/≈ₘ : Algebra (Σ Θ)
|T|_⦉_⦊/≈ₘ = record { Carrierₛ  = Herbrandₘ
                    ; isAlgebra = |T|_⦉_⦊/≈ₘ-isAlgebra
                    }

{-
|T|_⦉_⦊/≈ₘ-models : Models Θ |T|_⦉_⦊/≈ₘ
|T|_⦉_⦊/≈ₘ-models eq {θ} = begin
    subst |T|_⦉_⦊/≈ₘ θ lhs
  ≈⟨ IsEquivalence.reflexive ≈ₘ-isEquivalence (quotient-subst lhs) ⟩
    subst |T| (Σ Θ) ⦉ n ⦊ θ lhs
  ≈⟨ {!!} ⟩
    subst |T| (Σ Θ) ⦉ n ⦊ θ rhs
  ≈⟨ IsEquivalence.reflexive ≈ₘ-isEquivalence (quotient-subst rhs) ⟩
    subst |T|_⦉_⦊/≈ₘ θ rhs
  ∎
  where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
        rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

|T|_⦉_⦊/≈ₘ-isModel : IsModel Θ Herbrandₘ
|T|_⦉_⦊/≈ₘ-isModel = record { isAlgebra = |T|_⦉_⦊/≈ₘ-isAlgebra
                            ; models    = |T|_⦉_⦊/≈ₘ-models
                            }

|T|ₘ_⦉_⦊ : Model Θ
|T|ₘ_⦉_⦊ = record { Carrierₛ  = Herbrandₘ
                  ; isModel   = |T|_⦉_⦊/≈ₘ-isModel
                  }
-}
