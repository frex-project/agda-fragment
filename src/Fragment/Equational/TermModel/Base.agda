{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.TermModel.Base (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Quotient
open import Fragment.Algebra.TermAlgebra (Σ Θ)
open import Fragment.Algebra.FreeAlgebra

open import Fragment.Equational.Model
open import Fragment.Equational.Initial Θ

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)

data _≈ₘ_ : Expr → Expr → Set where
  refl  : ∀ {x} → x ≈ₘ x
  sym   : ∀ {x y} → x ≈ₘ y → y ≈ₘ x
  trans : ∀ {x y z} → x ≈ₘ y → y ≈ₘ z → x ≈ₘ z
  cong  : ∀ {arity} → (f : ops (Σ Θ) arity)
          → ∀ {xs ys} → Pointwise _≈ₘ_ xs ys
          → term f xs ≈ₘ term f ys
  model : ∀ {n} → (eq : eqs Θ n) → (θ : Environment n |T|)
          → subst |T| θ (proj₁ (Θ ⟦ eq ⟧ₑ)) ≈ₘ subst |T| θ (proj₂ (Θ ⟦ eq ⟧ₑ))

≈ₘ-isEquivalence : IsEquivalence _≈ₘ_
≈ₘ-isEquivalence = record { refl  = refl
                          ; sym   = sym
                          ; trans = trans
                          }

Herbrandₘ : Setoid _ _
Herbrandₘ = record { Carrier       = Expr
                   ; _≈_           = _≈ₘ_
                   ; isEquivalence = ≈ₘ-isEquivalence
                   }

≈ₘ : CompatibleEquivalence |T|
≈ₘ = record { _▲_           = _≈ₘ_
            ; isEquivalence = ≈ₘ-isEquivalence
            ; compatible    = cong
            }

≡⊂≈ₘ : underlyingEquivalence |T| ⊂ ≈ₘ
≡⊂≈ₘ x≡y = (IsEquivalence.reflexive ≈ₘ-isEquivalence) x≡y

|T|/≈ₘ : Algebra (Σ Θ)
|T|/≈ₘ = |T| / ≈ₘ

open import Relation.Binary.Reasoning.Setoid Herbrandₘ

|T|/≈ₘ-models : Models Θ |T|/≈ₘ
|T|/≈ₘ-models eq {θ} = begin
    subst |T|/≈ₘ θ lhs
  ≈⟨ IsEquivalence.reflexive ≈ₘ-isEquivalence (quotient-subst lhs) ⟩
    subst |T| θ lhs
  ≈⟨ model eq θ ⟩
    subst |T| θ rhs
  ≈⟨ IsEquivalence.reflexive ≈ₘ-isEquivalence (quotient-subst rhs) ⟩
    subst |T|/≈ₘ θ rhs
  ∎
  where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
        rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

|T|/≈ₘ-isModel : IsModel Θ Herbrandₘ
|T|/≈ₘ-isModel = record { isAlgebra = |T| / ≈ₘ -isAlgebra
                        ; models    = |T|/≈ₘ-models
                        }

|T|ₘ : Model Θ
|T|ₘ = record { Carrierₛ = Herbrandₘ
              ; isModel  = |T|/≈ₘ-isModel
              }
