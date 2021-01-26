{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Model where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Signature
open import Fragment.Algebra.FreeAlgebra

open import Level using (Level; _⊔_; suc)
open import Data.Product using (_,_)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level

_⊨⟨_⟩_ : ∀ {Σ n}
         → (S : Algebra Σ {a} {ℓ})
         → Environment n S
         → Eq Σ n
         → Set ℓ
S ⊨⟨ θ ⟩ (lhs , rhs) = subst S θ lhs ≈ subst S θ rhs
  where open Algebra S using (_≈_)

_⊨_ : ∀ {Σ n}
      → (Algebra Σ {a} {ℓ})
      → Eq Σ n
      → Set (a ⊔ ℓ)
_⊨_ S eq = ∀ {θ} → S ⊨⟨ θ ⟩ eq

Models : (Θ : Theory) → Algebra (Σ Θ) {a} {ℓ} → Set (a ⊔ ℓ)
Models Θ S = ∀ {n} → All (S ⊨_) (eqs Θ n)

module _ (Θ : Theory) (S : Setoid a ℓ) where

  record IsModel : Set (a ⊔ ℓ) where
    field
      isAlgebra : IsAlgebra (Σ Θ) S
      models    : Models Θ (algebra S isAlgebra)

    open IsAlgebra isAlgebra public

module _ (Θ : Theory) where

  record Model : Set (suc a ⊔ suc ℓ) where
    constructor model
    field
      Carrierₛ : Setoid a ℓ
      isModel  : IsModel Θ Carrierₛ

    open Setoid Carrierₛ public
    open IsModel isModel public

    Carrierₐ : Algebra (Σ Θ)
    Carrierₐ = algebra Carrierₛ isAlgebra
