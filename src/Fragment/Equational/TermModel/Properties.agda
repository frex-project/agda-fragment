{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.TermModel.Properties (Θ : Theory) where

open import Fragment.Equational.Model

open import Fragment.Equational.TermModel.Base Θ
open import Fragment.Equational.Initial Θ

open import Fragment.Algebra.TermAlgebra (Σ Θ)
  hiding (eval-cong; eval-hom; evalₕ; eval-args-universal; evalₕ-universal)
open import Fragment.Algebra.FreeAlgebra
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ) using (_≡ₕ_)

open import Level using (Level)
open import Function using (_∘_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Product using (proj₁; proj₂)

open import Relation.Binary using (IsEquivalence)
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a ℓ : Level

module _ (M : Model Θ {a} {ℓ}) where

  open Model M renaming (Carrierₐ to S)

  open import Relation.Binary.Reasoning.Setoid Carrierₛ
  open import Data.Vec.Relation.Binary.Equality.Setoid Carrierₛ using (_≋_)
  open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using ([]; _∷_)

  mutual
    eval-args-cong : ∀ {n} {xs ys : Vec Expr n}
                     → (PW.Pointwise _≈ₘ_) xs ys
                     → (eval-args S xs) ≋ (eval-args S ys)
    eval-args-cong [] = []
    eval-args-cong (x ∷ xs) = (eval-cong x) ∷ (eval-args-cong xs)

    eval-cong : Congruent _≈ₘ_ _≈_ (eval S)
    eval-cong (refl {x})        = Model.refl M {eval S x}
    eval-cong (sym x≈ₘy)        = Model.sym M (eval-cong x≈ₘy)
    eval-cong (trans x≈ₘy y≈ₘz) = Model.trans M (eval-cong x≈ₘy) (eval-cong y≈ₘz)
    eval-cong (cong f xs≈ₘys)   = ⟦⟧-cong f (eval-args-cong xs≈ₘys)
    eval-cong (model eq θ)      = begin
        eval S (subst |T| θ (proj₁ (Θ ⟦ eq ⟧ₑ)))
      ≈⟨ subst-eval {S = S} {θ = θ} {x = proj₁ (Θ ⟦ eq ⟧ₑ)} ⟩
        subst S (eval S ∘ θ) (proj₁ (Θ ⟦ eq ⟧ₑ))
      ≈⟨ models eq ⟩
        subst S (eval S ∘ θ) (proj₂ (Θ ⟦ eq ⟧ₑ))
      ≈⟨ Model.sym M (subst-eval {S = S} {θ = θ} {x = proj₂ (Θ ⟦ eq ⟧ₑ)}) ⟩
        eval S (subst |T| θ (proj₂ (Θ ⟦ eq ⟧ₑ)))
      ∎

  -- FIXME duplicates code in Fragment.Algebra.TermAlgebra.Properties
  eval-hom : Homomorphic |T|/≈ₘ S (eval S)
  eval-hom f xs = reflexive (PE.cong ⟦ f ⟧ (eval-args≡map S))

  evalₕ : |T|/≈ₘ →ₕ S
  evalₕ = record { h      = eval S
                 ; h-cong = eval-cong
                 ; h-hom  = eval-hom
                 }

  -- FIXME duplicates code in Fragment.Algebra.TermAlgebra.Properties
  mutual
    eval-args-universal : (H : |T|/≈ₘ →ₕ S)
                          → ∀ {arity} {xs : Vec Expr arity}
                          → map (_→ₕ_.h H) xs ≋ eval-args S xs
    eval-args-universal H {_} {[]}     = PW.[]
    eval-args-universal H {_} {x ∷ xs} =
      PW._∷_ (evalₕ-universal H {x}) (eval-args-universal H {_} {xs})

    evalₕ-universal : (H : |T|/≈ₘ →ₕ S) → H ≡ₕ evalₕ
    evalₕ-universal H {term f xs} = begin
        h (term f xs)
      ≈⟨ Model.sym M (h-hom f xs) ⟩
        ⟦ f ⟧ (map h xs)
      ≈⟨ ⟦⟧-cong f (eval-args-universal H) ⟩
        ⟦ f ⟧ (eval-args S xs)
      ≡⟨⟩
        eval S (term f xs)
      ∎
      where open _→ₕ_ H


|T|ₘ-isInitial : IsInitial |T|ₘ
|T|ₘ-isInitial = record { []_       =  evalₕ
                        ; universal = λ {_} {_} {S} → evalₕ-universal S
                        }
