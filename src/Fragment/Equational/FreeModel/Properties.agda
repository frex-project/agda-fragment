{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.FreeModel.Properties where

open import Fragment.Algebra.Signature renaming (_⦉_⦊ to _⦉_⦊ₜ)
open import Fragment.Algebra.FreeAlgebra
  using ( subst
        ; subst-subst
        ; subst-args
        ; subst-args≡map
        ; Environment
        ; |T|_⦉_⦊
        ; |T|_⦉_⦊-⟦_⟧
        )

open import Fragment.Equational.Theory
open import Fragment.Equational.Model
open import Fragment.Equational.FreeModel.Base

open import Level using (Level; _⊔_)
open import Function using (_∘_; _$_)

open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ {Θ n}
  (M : Model Θ {a} {ℓ})
  (θ : Environment n (Model.Carrierₐ M))
  where

  open Model M renaming (Carrierₐ to S; Carrier to A)

  open import Fragment.Algebra.Homomorphism (Σ Θ)
  open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ) using (_≡ₕ_)
  open import Fragment.Equational.TermModel.ProvableEquivalence Θ (|T| (Σ Θ) ⦉ n ⦊)

  open import Relation.Binary.Reasoning.Setoid Carrierₛ
  open import Data.Vec.Relation.Binary.Equality.Setoid Carrierₛ
    using (_≋_; ≋-isEquivalence)
  open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using ([]; _∷_)

  open import Fragment.Algebra.TermAlgebra ((Σ Θ) ⦉ n ⦊ₜ)

  -- FIXME this definition is duplicated from Fragment.Algebra.FreeAlgebra.Properties
  Substitution : (Expr → A) → Set a
  Substitution f = ∀ {k : Fin n}
                   → f (term (inj₂ k) []) ≡ θ k

  Substitutionₕ : (|T| Θ ⦉ n ⦊/≈ₘ) →ₕ S → Set a
  Substitutionₕ H = Substitution (_→ₕ_.h H)

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

  substitution-subst : Substitution (subst S θ)
  substitution-subst = PE.refl

  substitutionₕ-substₕ : Substitutionₕ substₕ
  substitutionₕ-substₕ = substitution-subst

  mutual
    subst-args-universal : (H : (|T| Θ ⦉ n ⦊/≈ₘ) →ₕ S)
                           → Substitutionₕ H
                           → ∀ {arity} {xs : Vec Expr arity}
                           → map (_→ₕ_.h H) xs ≋ subst-args S θ xs
    subst-args-universal H _       {_} {[]}     = PW.[]
    subst-args-universal H h-subst {_} {x ∷ xs} =
      PW._∷_
        (substₕ-universal H h-subst {x})
        (subst-args-universal H h-subst {_} {xs})

    substₕ-universal : (H : (|T| Θ ⦉ n ⦊/≈ₘ) →ₕ S)
                       → Substitutionₕ H
                       → H ≡ₕ substₕ
    substₕ-universal H h-subst {term (inj₂ k) []} = reflexive (h-subst {k})
    substₕ-universal H h-subst {term (inj₁ f) []} = Model.sym M (h-hom f [])
      where open _→ₕ_ H
    substₕ-universal H h-subst {term f (x ∷ xs)}  = begin
        h (term f (x ∷ xs))
      ≈⟨ Model.sym M (h-hom f (x ∷ xs)) ⟩
        ⟦ f ⟧ (map h (x ∷ xs))
      ≈⟨ ⟦⟧-cong f (subst-args-universal H h-subst) ⟩
        ⟦ f ⟧ (subst-args S θ (x ∷ xs))
      ≡⟨⟩
        subst S θ (term f (x ∷ xs))
      ∎
      where open _→ₕ_ H
