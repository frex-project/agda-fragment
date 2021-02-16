{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.FreeModel.Properties where

open import Fragment.Algebra.Signature renaming (_⦉_⦊ to _⦉_⦊ₜ)
open import Fragment.Algebra.FreeAlgebra
  hiding (subst-cong; subst-hom; substₕ; substₕ-universal)

open import Fragment.Equational.Theory
open import Fragment.Equational.Model
open import Fragment.Equational.FreeModel.Base

open import Level using (Level; _⊔_)
open import Function using (_∘_; _$_)

open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary using (IsEquivalence)
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a ℓ : Level

module _ {Θ n}
  (M : Model Θ {a} {ℓ})
  (θ : Environment n (Model.Carrierₐ M))
  where

  open Model M renaming (Carrierₐ to S)

  open import Fragment.Algebra.Homomorphism (Σ Θ)
  open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ) using (_≡ₕ_)
  open import Fragment.Equational.TermModel.ProvableEquivalence Θ (|T| (Σ Θ) ⦉ n ⦊)

  open import Relation.Binary.Reasoning.Setoid Carrierₛ
  open import Data.Vec.Relation.Binary.Equality.Setoid Carrierₛ
    using (_≋_; ≋-isEquivalence)
  open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using ([]; _∷_)

  open import Fragment.Algebra.TermAlgebra ((Σ Θ) ⦉ n ⦊ₜ)

  subst-hom : Homomorphic |T| Θ ⦉ n ⦊/≈ₘ S (subst S θ)
  subst-hom {_} f []       = Model.refl M
  subst-hom {m} f (x ∷ xs) =
    ⟦⟧-cong f $
      IsEquivalence.reflexive
        (≋-isEquivalence m)
        (subst-args≡map S θ {_} {x ∷ xs})

  mutual
    subst-args-cong : ∀ {arity} {xs ys : Vec Expr arity}
                      → (PW.Pointwise _≈ₘ_) xs ys
                      → (subst-args S θ xs) ≋ (subst-args S θ ys)
    subst-args-cong []       = []
    subst-args-cong (x ∷ xs) = (subst-cong x) ∷ subst-args-cong xs

    subst-cong : Congruent _≈ₘ_ _≈_ (subst S θ)
    subst-cong refl              = Model.refl M
    subst-cong (sym x≈ₘy)        = Model.sym M (subst-cong x≈ₘy)
    subst-cong (trans x≈ₘy y≈ₘz) = Model.trans M (subst-cong x≈ₘy) (subst-cong y≈ₘz)
    subst-cong (cong f {xs = xs} {ys = ys} xs≈ₘys) = begin
        subst S θ (|T| Σ Θ ⦉ n ⦊-⟦ f ⟧ xs)
      ≈⟨ Model.sym M (subst-hom f xs) ⟩
         ⟦ f ⟧ (map (subst S θ) xs)
      ≡⟨ PE.cong ⟦ f ⟧ (subst-args≡map S θ) ⟩
         ⟦ f ⟧ (subst-args S θ xs)
      ≈⟨ ⟦⟧-cong f (subst-args-cong xs≈ₘys) ⟩
         ⟦ f ⟧ (subst-args S θ ys)
      ≡⟨ PE.sym (PE.cong ⟦ f ⟧ (subst-args≡map S θ)) ⟩
         ⟦ f ⟧ (map (subst S θ) ys)
      ≈⟨ subst-hom f ys ⟩
        subst S θ (|T| Σ Θ ⦉ n ⦊-⟦ f ⟧ ys)
      ∎
    subst-cong (model eq θ') = begin
        subst S θ (subst |T| Σ Θ ⦉ n ⦊ θ' (proj₁ (Θ ⟦ eq ⟧ₑ)))
        ≈⟨ subst-subst {S = S} {x = proj₁ (Θ ⟦ eq ⟧ₑ)} ⟩
        subst S ((subst S θ) ∘ θ') (proj₁ (Θ ⟦ eq ⟧ₑ))
        ≈⟨ models eq ⟩
        subst S ((subst S θ) ∘ θ') (proj₂ (Θ ⟦ eq ⟧ₑ))
        ≈⟨ Model.sym M (subst-subst {S = S} {x = proj₂ (Θ ⟦ eq ⟧ₑ)}) ⟩
        subst S θ (subst |T| Σ Θ ⦉ n ⦊ θ' (proj₂ (Θ ⟦ eq ⟧ₑ)))
        ∎

  substₕ : |T| Θ ⦉ n ⦊/≈ₘ →ₕ S
  substₕ = record { h      = subst S θ
                  ; h-cong = subst-cong
                  ; h-hom  = subst-hom
                  }
