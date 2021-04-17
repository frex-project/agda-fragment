{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Model.Synthetic (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra (Σ Θ)
open import Fragment.Algebra.Free (Σ Θ)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Quotient (Σ Θ)
open import Fragment.Equational.Model.Base Θ
  using (Model; IsModel; Models)

open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a ℓ : Level

module _ (A : Algebra {a} {ℓ}) where

  infix 4 _≊_

  data _≊_ : ∥ A ∥ → ∥ A ∥ → Set (a ⊔ ℓ) where
    refl    : ∀ {x} → x ≊ x
    sym     : ∀ {x y} → x ≊ y → y ≊ x
    trans   : ∀ {x y z} → x ≊ y → y ≊ z → x ≊ z
    inherit : ∀ {x y} → x =[ A ] y → x ≊ y
    cong    : ∀ {n} → (f : ops (Σ Θ) n)
              → ∀ {xs ys} → Pointwise _≊_ xs ys
              → A ⟦ f ⟧ xs ≊ A ⟦ f ⟧ ys
    model   : ∀ {n} → (eq : eqs Θ n) → (θ : Env A n)
              → ∣ inst A θ ∣ (proj₁ (Θ ⟦ eq ⟧ₑ))
                ≊ ∣ inst A θ ∣ (proj₂ (Θ ⟦ eq ⟧ₑ))

  ≊-isEquivalence : IsEquivalence _≊_
  ≊-isEquivalence = record { refl  = refl
                           ; sym   = sym
                           ; trans = trans
                           }

  ≊ : CompatibleEquivalence A
  ≊ = record { _≈_           = _≊_
             ; isEquivalence = ≊-isEquivalence
             ; compatible    = cong
             }

  Synthetic : Model
  Synthetic = record { ∥_∥/≈   = setoid ≊
                     ; isModel = isModel
                     }
    where open Setoid (setoid ≊)
          open import Relation.Binary.Reasoning.Setoid (setoid ≊)

          models : Models (A / ≊)
          models eq θ = begin
              ∣ inst (A / ≊) θ ∣ lhs
            ≡⟨ PE.sym (∣inst∣-quot (≊) {x = lhs} θ) ⟩
              ∣ inst A θ ∣ lhs
            ≈⟨ model eq θ ⟩
              ∣ inst A θ ∣ rhs
            ≡⟨ ∣inst∣-quot (≊) {x = rhs} θ ⟩
              ∣ inst (A / ≊) θ ∣ rhs
            ∎
            where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
                  rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

          isModel : IsModel (setoid ≊)
          isModel = record { isAlgebra = A / ≊ -isAlgebra
                           ; models    = models
                           }

J : ℕ → Model
J = Synthetic ∘ F
