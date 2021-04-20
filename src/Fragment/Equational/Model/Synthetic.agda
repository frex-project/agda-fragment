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
open import Fragment.Setoid.Morphism using (_·_)

open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using (map)
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
    axiom   : ∀ {n} → (eq : eqs Θ n) → (θ : Env A n)
              → ∣ inst A θ ∣ (proj₁ (Θ ⟦ eq ⟧ₑ))
                ≊ ∣ inst A θ ∣ (proj₂ (Θ ⟦ eq ⟧ₑ))

  private

    ≊-isEquivalence : IsEquivalence _≊_
    ≊-isEquivalence = record { refl  = refl
                             ; sym   = sym
                             ; trans = trans
                             }

  instance
    ≊-isDenom : IsDenominator A _≊_
    ≊-isDenom = record { isEquivalence = ≊-isEquivalence
                       ; isCompatible  = cong
                       ; isCoarser     = inherit
                       }

  Synthetic : Model
  Synthetic = record { ∥_∥/≈   = ∥ A ∥/ _≊_
                     ; isModel = isModel
                     }
    where open module T = Setoid (∥ A ∥/ _≊_)
          open import Relation.Binary.Reasoning.Setoid (∥ A ∥/ _≊_)

          models : Models (A / _≊_)
          models eq θ = begin
              ∣ inst (A / _≊_) θ ∣ lhs
            ≈⟨ T.sym (lemma {x = lhs}) ⟩
              ∣ (inc A _≊_) ⊙ (inst A θ) ∣ lhs
            ≈⟨ axiom eq θ ⟩
              ∣ (inc A _≊_) ⊙ (inst A θ) ∣ rhs
            ≈⟨ lemma {x = rhs} ⟩
              ∣ inst (A / _≊_) θ ∣ rhs
            ∎
            where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
                  rhs = proj₂ (Θ ⟦ eq ⟧ₑ)
                  lemma = inst-universal (A / _≊_) θ
                              {h = (inc A _≊_) ⊙ (inst A θ) }
                              (λ x → PE.refl)

          isModel : IsModel (∥ A ∥/ _≊_)
          isModel = record { isAlgebra = A / _≊_ -isAlgebra
                           ; models    = models
                           }

J : ℕ → Model
J = Synthetic ∘ F
