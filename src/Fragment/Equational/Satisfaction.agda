{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Equational.Satisfaction {Σ : Signature} where

open import Fragment.Equational.Theory hiding (Σ)
open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.FreeAlgebra Σ

open import Level using (Level; _⊔_)
open import Data.Product using (_,_)
open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level

_⊨⟨_⟩_ : ∀ {n} → (S : Algebra {a} {ℓ})
         → Environment n S
         → Eq Σ n
         → Set ℓ
S ⊨⟨ θ ⟩ (lhs , rhs) = subst S θ lhs ≈ subst S θ rhs
  where open Setoid (∥ S ∥/≈)

_⊨_ : ∀ {n} → Algebra {a} {ℓ} → Eq Σ n → Set (a ⊔ ℓ)
_⊨_ S eq = ∀ {θ} → S ⊨⟨ θ ⟩ eq
