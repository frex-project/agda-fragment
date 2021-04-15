{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Blackstone where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra hiding (∥_∥/≈)

open import Fragment.Algebra.Blackstone

open import Level using (Level; _⊔_; suc)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)

open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level

Eq : (Σ : Signature) → (n : ℕ) → Set
Eq Σ n = Term Σ (Fin n) × Term Σ (Fin n)

record Theory : Set₁ where
  field
    Σ     : Signature
    eqs   : ℕ → Set
    _⟦_⟧ₑ : ∀ {arity : ℕ} → (eqs arity) → Eq Σ arity

  open Signature Σ

open Theory public

Environment : ∀ {a ℓ} {Σ : Signature} → ℕ → Algebra Σ {a} {ℓ} → Set a
Environment n S = Fin n → ∥ S ∥

module _ {Σ : Signature} where

  open import Fragment.Algebra.Homomorphism Σ

  _⊨⟨_⟩_ : ∀ {n} → (S : Algebra Σ {a} {ℓ})
           → Environment n S
           → Eq Σ n
           → Set ℓ
  S ⊨⟨ θ ⟩ (lhs , rhs) =
    (∥ substₕ Σ S (lift θ) ∥ₕ lhs) ≈ (∥ substₕ Σ S (lift θ) ∥ₕ rhs)
    where open import Fragment.Algebra.Algebra using (∥_∥/≈)
          open Setoid (∥ S ∥/≈)

  _⊨_ : ∀ {n} → Algebra Σ {a} {ℓ} → Eq Σ n → Set (a ⊔ ℓ)
  _⊨_ S eq = ∀ {θ} → S ⊨⟨ θ ⟩ eq

module _ (Θ : Theory) where

  Models : Algebra (Σ Θ) {a} {ℓ} → Set (a ⊔ ℓ)
  Models S = ∀ {n} → (eq : eqs Θ n) → S ⊨ (Θ ⟦ eq ⟧ₑ)

  module _ (S : Setoid a ℓ) where

    record IsModel : Set (a ⊔ ℓ) where
      field
        isAlgebra : IsAlgebra (Σ Θ) S
        models    : Models (algebra S isAlgebra)

      open IsAlgebra isAlgebra public

  record Model : Set (suc a ⊔ suc ℓ) where
    constructor model
    field
      ∥_∥/≈   : Setoid a ℓ
      isModel : IsModel ∥_∥/≈

    ∥_∥ₐ : Algebra (Σ Θ)
    ∥_∥ₐ = algebra ∥_∥/≈ (IsModel.isAlgebra isModel)

    ∥_∥ₐ-models : Models ∥_∥ₐ
    ∥_∥ₐ-models = IsModel.models isModel

    open Algebra (algebra ∥_∥/≈ (IsModel.isAlgebra isModel)) hiding (∥_∥/≈) public

  open Model public
