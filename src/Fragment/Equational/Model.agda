{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Model (Θ : Theory) where

open import Fragment.Equational.Satisfaction {Σ Θ}
open import Fragment.Algebra.Algebra (Σ Θ) hiding (isAlgebra; ∥_∥/≈)

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level

Models : Algebra {a} {ℓ} → Set (a ⊔ ℓ)
Models S = ∀ {n} → (eq : eqs Θ n) → S ⊨ (Θ ⟦ eq ⟧ₑ)

module _ (S : Setoid a ℓ) where

  record IsModel : Set (a ⊔ ℓ) where
    field
      isAlgebra : IsAlgebra S
      models    : Models (algebra S isAlgebra)

    open IsAlgebra isAlgebra public

record Model : Set (suc a ⊔ suc ℓ) where
  constructor model
  field
    ∥_∥/≈   : Setoid a ℓ
    isModel : IsModel ∥_∥/≈

  ∥_∥ₐ : Algebra
  ∥_∥ₐ = algebra ∥_∥/≈ (IsModel.isAlgebra isModel)

  ∥_∥ₐ-models : Models ∥_∥ₐ
  ∥_∥ₐ-models = IsModel.models isModel

  open Algebra (algebra ∥_∥/≈ (IsModel.isAlgebra isModel)) hiding (∥_∥/≈)public

open Model public
