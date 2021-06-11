{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.Monoid where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Homomorphism
open import Fragment.Algebra.Free hiding (_~_)
open import Fragment.Algebra.Algebra
  using (Algebra; IsAlgebra; Interpretation; Congruence; algebra)

open import Fragment.Equational.Theory
open import Fragment.Equational.Theory.Bundles
open import Fragment.Equational.Theory.Combinators
open import Fragment.Equational.FreeExtension
open import Fragment.Equational.Model Θ-monoid

open import Fragment.Extensions.Semigroup

open import Level using (Level; _⊔_)

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ (A : Model {a} {ℓ}) (n : ℕ) where

  private

    open module A = Setoid ∥ A ∥/≈

    u : ∥ A ∥
    u = A ⟦ newₒ α ⟧ []

    _·_ : ∥ A ∥ → ∥ A ∥ → ∥ A ∥
    x · y = A ⟦ oldₒ • ⟧ (x ∷ y ∷ [])

    ·-cong : ∀ {x y z w} → x ≈ y → z ≈ w → x · z ≈ y · w
    ·-cong x≈y z≈w = (A ⟦ oldₒ • ⟧-cong) (x≈y ∷ z≈w ∷ [])

    ·-unitₗ : ∀ (x : ∥ A ∥) → u · x ≈ x
    ·-unitₗ x =
      ∥ A ∥ₐ-models (newₑ idₗ) (env (Σ Θ-monoid) {A = ∥ A ∥ₐ} (x ∷ []))

    ·-unitᵣ : ∀ (x : ∥ A ∥) → x · u ≈ x
    ·-unitᵣ x =
      ∥ A ∥ₐ-models (newₑ idᵣ) (env (Σ Θ-monoid) {A = ∥ A ∥ₐ} (x ∷ []))

    ·-assoc : ∀ (x y z : ∥ A ∥) → (x · y) · z ≈ x · (y · z)
    ·-assoc x y z =
      ∥ A ∥ₐ-models (oldₑ assoc) (env (Σ Θ-monoid) {A = ∥ A ∥ₐ} (x ∷ y ∷ z ∷ []))

    open FreeExtension Θ-semigroup SemigroupFrex

{-
    data ITree : Set a where
      e    : ITree
      tree : ∥ (forgetₑ A) [ n ] ∥ → ITree
-}
