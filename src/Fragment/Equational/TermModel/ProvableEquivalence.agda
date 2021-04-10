{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory
open import Fragment.Algebra.Algebra using (Algebra)

module Fragment.Equational.TermModel.ProvableEquivalence
  {a ℓ}
  (Θ : Theory)
  (S : Algebra (Σ Θ) {a} {ℓ})
  where

open import Fragment.Algebra.Signature using (ops)
open import Fragment.Algebra.Algebra (Σ Θ)
open import Fragment.Algebra.FreeAlgebra (Σ Θ)
open import Fragment.Algebra.Quotient (Σ Θ)

open import Level using (_⊔_)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Relation.Binary using (IsEquivalence)

data _≈ₘ_ : ∥ S ∥ → ∥ S ∥ → Set (a ⊔ ℓ) where
  refl  : ∀ {x} → x ≈ₘ x
  sym   : ∀ {x y} → x ≈ₘ y → y ≈ₘ x
  trans : ∀ {x y z} → x ≈ₘ y → y ≈ₘ z → x ≈ₘ z
  cong  : ∀ {arity} → (f : ops (Σ Θ) arity)
          → ∀ {xs ys} → Pointwise _≈ₘ_ xs ys
          → (S ⟦ f ⟧) xs ≈ₘ (S ⟦ f ⟧) ys
  model : ∀ {n} → (eq : eqs Θ n) → (θ : Environment n S)
          → subst S θ (proj₁ (Θ ⟦ eq ⟧ₑ)) ≈ₘ subst S θ (proj₂ (Θ ⟦ eq ⟧ₑ))

≈ₘ-isEquivalence : IsEquivalence _≈ₘ_
≈ₘ-isEquivalence = record { refl  = refl
                          ; sym   = sym
                          ; trans = trans
                          }

≈ₘ : CompatibleEquivalence S
≈ₘ = record { _≈_           = _≈ₘ_
            ; isEquivalence = ≈ₘ-isEquivalence
            ; compatible    = cong
            }
