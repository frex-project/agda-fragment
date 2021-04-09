{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory
open import Data.Nat using (ℕ)

module Fragment.Equational.FreeModel.Base
  (Θ : Theory)
  (n : ℕ)
  where

open import Fragment.Algebra.Algebra (Σ Θ)
open import Fragment.Algebra.Quotient (Σ Θ)
open import Fragment.Algebra.FreeAlgebra (Σ Θ)

open import Fragment.Equational.Model Θ
open import Fragment.Equational.TermModel (Θ ⦉ n ⦊ₜ)
open import Fragment.Equational.TermModel.ProvableEquivalence Θ (|T|⦉ n ⦊)

open import Data.Product using (proj₁; proj₂)
open import Relation.Binary using (IsEquivalence)

open import Relation.Binary.Reasoning.Setoid ∥ |T|⦉ n ⦊ / ≈ₘ ∥/≈

|T|⦉_⦊/≈ₘ-models : Models (|T|⦉ n ⦊ / ≈ₘ)
|T|⦉_⦊/≈ₘ-models eq {θ} = begin
    subst (|T|⦉ n ⦊ / ≈ₘ) θ lhs
  ≈⟨ reflexive (quotient-subst lhs) ⟩
    subst (|T|⦉ n ⦊) θ lhs
  ≈⟨ model eq θ ⟩
    subst (|T|⦉ n ⦊) θ rhs
  ≈⟨ reflexive (quotient-subst rhs) ⟩
    subst (|T|⦉ n ⦊ / ≈ₘ) θ rhs
  ∎
  where open IsEquivalence  ≈ₘ-isEquivalence
        lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
        rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

|T|⦉_⦊/≈ₘ-isModel : IsModel ∥ |T|⦉ n ⦊ / ≈ₘ ∥/≈
|T|⦉_⦊/≈ₘ-isModel = record { isAlgebra = |T|⦉ n ⦊ / ≈ₘ -isAlgebra
                           ; models    = |T|⦉_⦊/≈ₘ-models
                           }

|T|⦉_⦊/≈ₘ : Model
|T|⦉_⦊/≈ₘ = record { ∥_∥/≈   = ∥ |T|⦉ n ⦊ / ≈ₘ ∥/≈
                   ; isModel = |T|⦉_⦊/≈ₘ-isModel
                   }
