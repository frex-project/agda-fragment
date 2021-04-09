{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeModel.Properties (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ) using (_≡ₕ_)
open import Fragment.Algebra.FreeAlgebra (Σ Θ)
  using ( subst
        ; subst-subst
        ; subst-args
        ; subst-args≡map
        ; Substitution
        ; Environment
        ; |T|⦉_⦊
        ; term₁
        ; term₂
        )

open import Fragment.Equational.Model Θ
open import Fragment.Equational.FreeModel.Base Θ

open import Level using (Level; _⊔_)
open import Function using (_∘_; _$_)

open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ {n}
  (M : Model {a} {ℓ})
  (θ : Environment n ∥ M ∥ₐ)
  where

  open import Fragment.Algebra.TermAlgebra ((Σ Θ) ⦉ n ⦊)
  open import Fragment.Equational.TermModel.ProvableEquivalence Θ (|T|⦉ n ⦊) as E
    using (_≈ₘ_)

  open Setoid ∥ M ∥/≈

  open import Relation.Binary.Reasoning.Setoid ∥ M ∥/≈
  open import Data.Vec.Relation.Binary.Equality.Setoid ∥ M ∥/≈
    using (_≋_; ≋-isEquivalence)

  Substitutionₕ : ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ∥ M ∥ₐ → Set a
  Substitutionₕ h = Substitution ∥ M ∥ₐ θ ∥ h ∥ₕ

  subst-hom : Homomorphic ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ ∥ M ∥ₐ (subst ∥ M ∥ₐ θ)
  subst-hom {_} f []       = refl
  subst-hom {m} f (x ∷ xs) =
    (M ⟦⟧-cong) f $ ≋.reflexive (subst-args≡map ∥ M ∥ₐ θ {xs = x ∷ xs})
    where open module ≋ = IsEquivalence (≋-isEquivalence m)

  mutual
    subst-args-cong : ∀ {arity} {xs ys : Vec Expr arity}
                      → Pointwise _≈ₘ_ xs ys
                      → (subst-args ∥ M ∥ₐ θ xs) ≋ (subst-args ∥ M ∥ₐ θ ys)
    subst-args-cong []       = []
    subst-args-cong (x ∷ xs) = (subst-cong x) ∷ subst-args-cong xs

    subst-cong : Congruent _≈ₘ_ _≈_ (subst ∥ M ∥ₐ θ)
    subst-cong E.refl              = refl
    subst-cong (E.sym x≈ₘy)        = sym (subst-cong x≈ₘy)
    subst-cong (E.trans x≈ₘy y≈ₘz) = trans (subst-cong x≈ₘy) (subst-cong y≈ₘz)
    subst-cong (E.cong f {xs = xs} {ys = ys} xs≈ₘys) = begin
        subst ∥ M ∥ₐ θ ((|T|⦉ n ⦊/≈ₘ ⟦ f ⟧) xs)
      ≈⟨ sym (subst-hom f xs) ⟩
         (M ⟦ f ⟧) (map (subst ∥ M ∥ₐ θ) xs)
      ≡⟨ PE.cong (M ⟦ f ⟧) (subst-args≡map ∥ M ∥ₐ θ) ⟩
         (M ⟦ f ⟧) (subst-args ∥ M ∥ₐ θ xs)
      ≈⟨ (M ⟦⟧-cong) f (subst-args-cong xs≈ₘys) ⟩
         (M ⟦ f ⟧) (subst-args ∥ M ∥ₐ θ ys)
      ≡⟨ PE.sym (PE.cong (M ⟦ f ⟧) (subst-args≡map ∥ M ∥ₐ θ)) ⟩
         (M ⟦ f ⟧) (map (subst ∥ M ∥ₐ θ) ys)
      ≈⟨ subst-hom f ys ⟩
        subst ∥ M ∥ₐ θ ((|T|⦉ n ⦊/≈ₘ ⟦ f ⟧) ys)
      ∎
    subst-cong (E.model eq θ') = begin
        subst ∥ M ∥ₐ θ (subst |T|⦉ n ⦊ θ' (proj₁ (Θ ⟦ eq ⟧ₑ)))
      ≈⟨ subst-subst {S = ∥ M ∥ₐ} {x = proj₁ (Θ ⟦ eq ⟧ₑ)} ⟩
        subst ∥ M ∥ₐ ((subst ∥ M ∥ₐ θ) ∘ θ') (proj₁ (Θ ⟦ eq ⟧ₑ))
      ≈⟨ ∥ M ∥ₐ-models eq ⟩
        subst ∥ M ∥ₐ ((subst ∥ M ∥ₐ θ) ∘ θ') (proj₂ (Θ ⟦ eq ⟧ₑ))
      ≈⟨ sym (subst-subst {S = ∥ M ∥ₐ} {x = proj₂ (Θ ⟦ eq ⟧ₑ)}) ⟩
        subst ∥ M ∥ₐ θ (subst |T|⦉ n ⦊ θ' (proj₂ (Θ ⟦ eq ⟧ₑ)))
      ∎

  substₕ : ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ∥ M ∥ₐ
  substₕ = record { ∥_∥ₕ      = subst ∥ M ∥ₐ θ
                  ; ∥_∥ₕ-cong = subst-cong
                  ; ∥_∥ₕ-hom  = subst-hom
                  }

  substitution-subst : Substitution ∥ M ∥ₐ θ (subst ∥ M ∥ₐ θ)
  substitution-subst = PE.refl

  substitutionₕ-substₕ : Substitutionₕ substₕ
  substitutionₕ-substₕ = substitution-subst

  mutual
    subst-args-universal : (h : ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ∥ M ∥ₐ)
                           → Substitutionₕ h
                           → ∀ {arity} {xs : Vec Expr arity}
                           → map ∥ h ∥ₕ xs ≋ subst-args ∥ M ∥ₐ θ xs
    subst-args-universal h _       {xs = []}     = []
    subst-args-universal h h-subst {xs = x ∷ xs} =
        substₕ-universal h h-subst {x} ∷ subst-args-universal h h-subst {_} {xs}

    substₕ-universal : (h : ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ∥ M ∥ₐ)
                       → Substitutionₕ h
                       → h ≡ₕ substₕ
    substₕ-universal h h-subst {term₂ k} = reflexive (h-subst {k})
    substₕ-universal h h-subst {term₁ f} = sym (∥ h ∥ₕ-hom f [])
    substₕ-universal h h-subst {term f (x ∷ xs)}  = begin
        ∥ h ∥ₕ (term f (x ∷ xs))
      ≈⟨ sym (∥ h ∥ₕ-hom f (x ∷ xs)) ⟩
        (M ⟦ f ⟧) (map ∥ h ∥ₕ (x ∷ xs))
      ≈⟨ (M ⟦⟧-cong) f (subst-args-universal h h-subst) ⟩
        (M ⟦ f ⟧) (subst-args ∥ M ∥ₐ θ (x ∷ xs))
      ∎
