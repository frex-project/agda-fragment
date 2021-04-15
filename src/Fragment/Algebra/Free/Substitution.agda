{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Substitution (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Algebra.Free.Base Σ
open import Fragment.Algebra.Free.Monad Σ
open import Fragment.Algebra.Free.Evaluation Σ
open import Fragment.Setoid.Morphism

open import Level using (Level)
open import Data.Fin using (Fin)
open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a b ℓ₁ ℓ₂ : Level

∣sub∣ : ∀ {n} {A : Set a} → (Fin n → A) → BT A n → A
∣sub∣ θ (sta x) = x
∣sub∣ θ (dyn n) = θ n

module _ (S : Setoid a ℓ₁) where

  open Setoid S renaming (Carrier to A)

  ∣sub∣-cong : ∀ {n} (θ : Fin n → A)
               → Congruent (_≑_ S n) _≈_ (∣sub∣ θ)
  ∣sub∣-cong θ (sta x≈y) = x≈y
  ∣sub∣-cong θ (dyn x≡y) = reflexive (PE.cong θ x≡y)

  sub :  ∀ {n} (θ : Fin n → A) → BT/≑ S n ↝ S
  sub θ = record { ∣_∣      = ∣sub∣ θ
                 ; ∣_∣-cong = ∣sub∣-cong θ
                 }

subst : ∀ {n} {A : Algebra {a} {ℓ₁}}
        → (Fin n → ∥ A ∥)
        → Free ∥ A ∥/≈ [ n ] ⟿ A
subst {A = A} θ = eval A ⊙ fmap (sub ∥ A ∥/≈ θ)
