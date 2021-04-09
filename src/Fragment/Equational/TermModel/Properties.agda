{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.TermModel.Properties (Θ : Theory) where

open import Fragment.Algebra.TermAlgebra (Σ Θ)
  using (|T|; Expr; term; eval; eval-args; eval-args≡map)
open import Fragment.Algebra.FreeAlgebra (Σ Θ)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ) using (_≡ₕ_)

open import Fragment.Equational.Model Θ
open import Fragment.Equational.TermModel.Base Θ
open import Fragment.Equational.Initial Θ
open import Fragment.Equational.TermModel.ProvableEquivalence Θ |T| as E
  using (_≈ₘ_)

open import Level using (Level)
open import Function using (_∘_)

import Relation.Binary.PropositionalEquality as PE
open import Relation.Binary using (Setoid; IsEquivalence)

open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_; Pointwise)
open import Data.Product using (proj₁; proj₂)

private
  variable
    a ℓ : Level

module _ (M : Model {a} {ℓ}) where

  open Setoid ∥ M ∥/≈

  open import Relation.Binary.Reasoning.Setoid ∥ M ∥/≈
  open import Data.Vec.Relation.Binary.Equality.Setoid ∥ M ∥/≈ using (_≋_)

  mutual
    eval-args-cong : ∀ {arity} {xs ys : Vec Expr arity}
                     → Pointwise _≈ₘ_ xs ys
                     → (eval-args ∥ M ∥ₐ xs) ≋ (eval-args ∥ M ∥ₐ ys)
    eval-args-cong [] = []
    eval-args-cong (x ∷ xs) = (eval-cong x) ∷ (eval-args-cong xs)

    eval-cong : Congruent _≈ₘ_ ≈[ M ] (eval ∥ M ∥ₐ)
    eval-cong (E.refl {x})        = refl {eval ∥ M ∥ₐ x}
    eval-cong (E.sym x≈ₘy)        = sym (eval-cong x≈ₘy)
    eval-cong (E.trans x≈ₘy y≈ₘz) = trans (eval-cong x≈ₘy) (eval-cong y≈ₘz)
    eval-cong (E.cong f xs≈ₘys)   = (M ⟦⟧-cong) f (eval-args-cong xs≈ₘys)
    eval-cong (E.model eq θ)      = begin
        eval ∥ M ∥ₐ (subst |T| θ (proj₁ (Θ ⟦ eq ⟧ₑ)))
      ≈⟨ subst-eval {S = ∥ M ∥ₐ} {θ = θ} {x = proj₁ (Θ ⟦ eq ⟧ₑ)} ⟩
        subst ∥ M ∥ₐ (eval ∥ M ∥ₐ ∘ θ) (proj₁ (Θ ⟦ eq ⟧ₑ))
      ≈⟨ ∥ M ∥ₐ-models eq ⟩
        subst ∥ M ∥ₐ (eval ∥ M ∥ₐ ∘ θ) (proj₂ (Θ ⟦ eq ⟧ₑ))
      ≈⟨ sym (subst-eval {S = ∥ M ∥ₐ} {θ = θ} {x = proj₂ (Θ ⟦ eq ⟧ₑ)}) ⟩
        eval ∥ M ∥ₐ (subst |T| θ (proj₂ (Θ ⟦ eq ⟧ₑ)))
      ∎

  eval-hom : Homomorphic |T|/≈ₘ ∥ M ∥ₐ (eval ∥ M ∥ₐ)
  eval-hom f xs = reflexive (PE.cong (M ⟦ f ⟧) (eval-args≡map ∥ M ∥ₐ))

  evalₕ : |T|/≈ₘ →ₕ ∥ M ∥ₐ
  evalₕ = record { ∥_∥ₕ      = eval ∥ M ∥ₐ
                 ; ∥_∥ₕ-cong = eval-cong
                 ; ∥_∥ₕ-hom  = eval-hom
                 }

  mutual
    eval-args-universal : (h : |T|/≈ₘ →ₕ ∥ M ∥ₐ)
                          → ∀ {arity} {xs : Vec Expr arity}
                          → map ∥ h ∥ₕ xs ≋ eval-args ∥ M ∥ₐ xs
    eval-args-universal h {xs = []}     = []
    eval-args-universal h {xs = x ∷ xs} =
      evalₕ-universal h {x} ∷ eval-args-universal h {xs = xs}

    evalₕ-universal : (h : |T|/≈ₘ →ₕ ∥ M ∥ₐ) → h ≡ₕ evalₕ
    evalₕ-universal h {term f xs} = begin
        ∥ h ∥ₕ (term f xs)
      ≈⟨ sym (∥ h ∥ₕ-hom f xs) ⟩
        (M ⟦ f ⟧) (map ∥ h ∥ₕ xs)
      ≈⟨ (M ⟦⟧-cong) f (eval-args-universal h) ⟩
        (M ⟦ f ⟧) (eval-args ∥ M ∥ₐ xs)
      ∎

|T|ₘ-isInitial : IsInitial |T|ₘ
|T|ₘ-isInitial = record { []_       =  evalₕ
                        ; universal = λ {_} {_} {S} → evalₕ-universal S
                        }
