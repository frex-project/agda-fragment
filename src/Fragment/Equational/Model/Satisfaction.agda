{-# OPTIONS --without-K --exact-split --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Equational.Model.Satisfaction {Σ : Signature} where

open import Fragment.Equational.Theory.Base hiding (Σ)
open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Free Σ
open import Fragment.Algebra.Homomorphism Σ

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level

_⊨⟨_⟩_ : ∀ {n} → (A : Algebra {a} {ℓ})
         → Env A n → Eq Σ n → Set ℓ
A ⊨⟨ θ ⟩ (lhs , rhs) =
  ∣ inst A θ ∣ lhs =[ A ] ∣ inst A θ ∣ rhs

_⊨_ : ∀ {n} → Algebra {a} {ℓ} → Eq Σ n → Set (a ⊔ ℓ)
_⊨_ S eq = ∀ θ → S ⊨⟨ θ ⟩ eq
