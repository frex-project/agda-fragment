{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Algebra (Σ : Signature) where

open import Level using (Level; _⊔_; suc)
open import Function using (id)
open import Data.Vec
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ (S : Setoid a ℓ) where

  open import Data.Vec.Relation.Binary.Equality.Setoid S using (_≋_)

  open Setoid S renaming (Carrier to A)

  Interpretation : Set a
  Interpretation = ∀ {arity} → (f : ops Σ arity) → Vec A arity → A

  Congruence : Interpretation → Set (a ⊔ ℓ)
  Congruence ⟦_⟧ = ∀ {arity}
                   → (f : ops Σ arity)
                   → ∀ {xs ys} → xs ≋ ys → ⟦ f ⟧ xs ≈ ⟦ f ⟧ ys

  record IsAlgebra : Set (a ⊔ ℓ) where
    field
      ⟦_⟧     : Interpretation
      ⟦⟧-cong : Congruence ⟦_⟧

record Algebra : Set (suc a ⊔ suc ℓ) where
  constructor algebra
  field
    ∥_∥/≈           : Setoid a ℓ
    ∥_∥/≈-isAlgebra : IsAlgebra ∥_∥/≈

  ∥_∥ : Set a
  ∥_∥ = Setoid.Carrier ∥_∥/≈

  infix 10 _⟦_⟧_

  _⟦_⟧_ : Interpretation (∥_∥/≈)
  _⟦_⟧_ = IsAlgebra.⟦_⟧ ∥_∥/≈-isAlgebra

  _⟦_⟧-cong : Congruence (∥_∥/≈) (_⟦_⟧_)
  _⟦_⟧-cong = IsAlgebra.⟦⟧-cong ∥_∥/≈-isAlgebra

  ≈[_] : Rel ∥_∥ ℓ
  ≈[_] = Setoid._≈_ ∥_∥/≈

  ≈[_]-isEquivalence : IsEquivalence ≈[_]
  ≈[_]-isEquivalence = Setoid.isEquivalence ∥_∥/≈

open Algebra public

infix 5 ≈-syntax

≈-syntax : (A : Algebra {a} {ℓ}) → ∥ A ∥ → ∥ A ∥ → Set ℓ
≈-syntax A x y = Setoid._≈_ ∥ A ∥/≈ x y

syntax ≈-syntax A x y = x =[ A ] y
