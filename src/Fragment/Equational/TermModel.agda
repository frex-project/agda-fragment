{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.TermModel (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.TermAlgebra (Σ Θ)
open import Fragment.Algebra.Algebra
open import Fragment.Algebra.FreeAlgebra
open import Fragment.Equational.Model

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)

private
  variable
    a ℓ : Level

module _ (S : Algebra (Σ Θ) {a} {ℓ}) where
  
  open Algebra S using (_≈_; ⟦_⟧) renaming (Carrier to A)

  data _≈ₘ_ : A → A → Set (a ⊔ ℓ) where
    refl  : ∀ {x} → x ≈ₘ x
    sym   : ∀ {x y} → x ≈ₘ y → y ≈ₘ x
    trans : ∀ {x y z} → x ≈ₘ y → y ≈ₘ z → x ≈ₘ z
    cong  : ∀ {arity} → (f : ops (Σ Θ) arity)
            → ∀ {xs ys} → Pointwise _≈ₘ_ xs ys
            → ⟦ f ⟧ xs ≈ₘ ⟦ f ⟧ ys
    model : ∀ {x y} → {n : ℕ} → (eq : eqs Θ n) → (θ : Environment n S)
            → x ≈ subst S θ (proj₁ (Θ ⟦ eq ⟧ₑ))
            → y ≈ subst S θ (proj₂ (Θ ⟦ eq ⟧ₑ))
            → x ≈ₘ y

  ≈ₘ-isEquivalence : IsEquivalence _≈ₘ_
  ≈ₘ-isEquivalence = record { refl  = refl
                            ; sym   = sym
                            ; trans = trans
                            }

Herbrandₘ : Setoid _ _
Herbrandₘ = record { Carrier       = Expr
                   ; isEquivalence = ≈ₘ-isEquivalence |T|
                   }

|T|ₘ-isAlgebra : IsAlgebra (Σ Θ) Herbrandₘ
|T|ₘ-isAlgebra = record { ⟦_⟧     = term
                        ; ⟦⟧-cong = cong
                        }

|T|ₘ : Algebra (Σ Θ)
|T|ₘ = record { Carrierₛ  = Herbrandₘ
              ; isAlgebra = |T|ₘ-isAlgebra
              }

|T|ₘ-models : Models Θ |T|ₘ
|T|ₘ-models eq {θ} = ?
