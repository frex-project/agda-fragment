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
open import Fragment.Equational.TermModel.ProvableEquivalence Θ (|T| (Σ Θ) ⦉ n ⦊)

open import Data.Product using (proj₁; proj₂)
open import Relation.Binary using (IsEquivalence)

|T|_⦉_⦊/≈ₘ : Algebra (Σ Θ)
|T|_⦉_⦊/≈ₘ = |T| (Σ Θ) ⦉ n ⦊ / ≈ₘ

open Algebra |T|_⦉_⦊/≈ₘ renaming (Carrierₛ to A)

open import Relation.Binary.Reasoning.Setoid A

|T|_⦉_⦊/≈ₘ-models : Models Θ |T|_⦉_⦊/≈ₘ
|T|_⦉_⦊/≈ₘ-models eq {θ} = begin
    subst |T|_⦉_⦊/≈ₘ θ lhs
  ≈⟨ IsEquivalence.reflexive ≈ₘ-isEquivalence (quotient-subst lhs) ⟩
    subst (|T| (Σ Θ) ⦉ n ⦊) θ lhs
  ≈⟨ model eq θ ⟩
    subst (|T| (Σ Θ) ⦉ n ⦊) θ rhs
  ≈⟨ IsEquivalence.reflexive ≈ₘ-isEquivalence (quotient-subst rhs) ⟩
    subst |T|_⦉_⦊/≈ₘ θ rhs
  ∎
  where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
        rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

|T|_⦉_⦊/≈ₘ-isModel : IsModel Θ A
|T|_⦉_⦊/≈ₘ-isModel = record { isAlgebra = isAlgebra
                            ; models    = |T|_⦉_⦊/≈ₘ-models
                            }

|T|ₘ_⦉_⦊ : Model Θ
|T|ₘ_⦉_⦊ = record { Carrierₛ  = A
                  ; isModel   = |T|_⦉_⦊/≈ₘ-isModel
                  }
