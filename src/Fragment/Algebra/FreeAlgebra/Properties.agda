{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.FreeAlgebra.Properties (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.FreeAlgebra.Base Σ
open import Fragment.Algebra.FreeAlgebra.Definitions Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ using (_≡ₕ_)

open import Level using (Level; _⊔_)
open import Function using (_$_; _∘_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Data.Vec using (Vec; []; _∷_; map)

private
  variable
    a b ℓ₁ ℓ₂ : Level

module _ {n} (S : Algebra {a} {ℓ₁}) (θ : Environment n S) where

  open Setoid ∥ S ∥/≈

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ n ⦊) using (Expr; term)

  open import Relation.Binary.Reasoning.Setoid ∥ S ∥/≈
  open import Data.Vec.Relation.Binary.Equality.Setoid ∥ S ∥/≈

  Substitution : (Expr → ∥ S ∥) → Set a
  Substitution f = ∀ {k : Fin n}
                   → f (term₂ k) ≡ θ k

  Substitutionₕ : (|T|⦉ n ⦊) →ₕ S → Set a
  Substitutionₕ f = Substitution ∥ f ∥ₕ

  mutual
    subst-args : ∀ {arity} → Vec Expr arity → Vec ∥ S ∥ arity
    subst-args []       = []
    subst-args (x ∷ xs) = (subst x) ∷ (subst-args xs)

    subst : Expr → ∥ S ∥
    subst (term₂ k)         = θ k
    subst (term₁ f)         = (S ⟦ f ⟧) []
    subst (term f (x ∷ xs)) = (S ⟦ f ⟧) (subst-args (x ∷ xs))

  subst-args≡map : ∀ {arity} {xs : Vec Expr arity}
                   → map subst xs ≡ subst-args xs
  subst-args≡map {_} {[]}     = PE.refl
  subst-args≡map {_} {x ∷ xs} = PE.cong (subst x ∷_) (subst-args≡map {xs = xs})

  subst-cong : Congruent _≡_ _≈_ subst
  subst-cong x≡y = reflexive (PE.cong subst x≡y)

  subst-hom : Homomorphic (|T|⦉ n ⦊) S subst
  subst-hom {_} f []       = refl
  subst-hom {m} f (x ∷ xs) =
    (S ⟦⟧-cong) f $ ≋.reflexive (subst-args≡map {xs = x ∷ xs})
    where open module ≋ = IsEquivalence (≋-isEquivalence m)

  substₕ : |T|⦉ n ⦊ →ₕ S
  substₕ = record { ∥_∥ₕ      = subst
                  ; ∥_∥ₕ-cong = subst-cong
                  ; ∥_∥ₕ-hom  = subst-hom
                  }

  substitution-subst : Substitution subst
  substitution-subst = PE.refl

  substitutionₕ-substₕ : Substitutionₕ substₕ
  substitutionₕ-substₕ = substitution-subst

  mutual
    subst-args-universal : (h : (|T|⦉ n ⦊) →ₕ S)
                           → Substitutionₕ h
                           → ∀ {arity} {xs : Vec Expr arity}
                           → map ∥ h ∥ₕ xs ≋ subst-args xs
    subst-args-universal h _       {_} {[]}     = []
    subst-args-universal h h-subst {_} {x ∷ xs} =
        substₕ-universal h h-subst {x} ∷
        subst-args-universal h h-subst {_} {xs}

    substₕ-universal : (h : (|T|⦉ n ⦊) →ₕ S)
                       → Substitutionₕ h
                       → h ≡ₕ substₕ
    substₕ-universal h h-subst {term₂ k} = reflexive (h-subst {k})
    substₕ-universal h _       {term₁ f} = sym (∥ h ∥ₕ-hom f [])
    substₕ-universal h h-subst {term f (x ∷ xs)} = begin
        ∥ h ∥ₕ (term f (x ∷ xs))
      ≈⟨ sym (∥ h ∥ₕ-hom f (x ∷ xs)) ⟩
        (S ⟦ f ⟧) (map ∥ h ∥ₕ (x ∷ xs))
      ≈⟨ (S ⟦⟧-cong) f (subst-args-universal h h-subst) ⟩
        (S ⟦ f ⟧) (subst-args (x ∷ xs))
      ≡⟨⟩
        subst (term f (x ∷ xs))
      ∎

module _ {n} {S : Algebra {a} {ℓ₁}} where

  open Setoid ∥ S ∥/≈

  open import Data.Vec.Relation.Binary.Equality.Setoid ∥ S ∥/≈ using (_≋_)
  open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ n ⦊) using (Expr; term)
  open import Fragment.Algebra.TermAlgebra Σ hiding (Expr)

  mutual
    subst-eval-args : ∀ {arity}
                      → {θ : Environment n |T|}
                      → {xs : Vec Expr arity}
                      → eval-args S (subst-args |T| θ xs)
                        ≋ subst-args S (eval S ∘ θ) xs
    subst-eval-args {θ = _} {xs = []}     = []
    subst-eval-args {θ = θ} {xs = x ∷ xs} = subst-eval {θ} {x} ∷ subst-eval-args

    subst-eval : ∀ {θ : Environment n |T|}
                 → evalₕ S ∘ₕ (substₕ |T| θ) ≡ₕ substₕ S (eval S ∘ θ)
    subst-eval {x = term₂ k}         = refl
    subst-eval {x = term₁ f}         = refl
    subst-eval {x = term f (x ∷ xs)} = (S ⟦⟧-cong) f (subst-eval-args {xs = x ∷ xs})

  mutual
    subst-subst-args : ∀ {m arity}
                       → {θ : Environment m S}
                       → {θ' : Environment n |T|⦉ m ⦊}
                       → {xs : Vec Expr arity}
                       → subst-args S θ (subst-args |T|⦉ m ⦊ θ' xs)
                         ≋  subst-args S ((subst S θ) ∘ θ') xs
    subst-subst-args {xs = []} = []
    subst-subst-args {xs = x ∷ xs} = subst-subst {x = x} ∷ subst-subst-args

    subst-subst : ∀ {m}
                  → {θ : Environment m S}
                  → {θ' : Environment n |T|⦉ m ⦊}
                  → substₕ S θ ∘ₕ substₕ |T|⦉ m ⦊ θ' ≡ₕ substₕ S ((subst S θ) ∘ θ')
    subst-subst {x = term₂ k}         = refl
    subst-subst {x = term₁ f}         = refl
    subst-subst {x = term f (x ∷ xs)} = (S ⟦⟧-cong) f (subst-subst-args {xs = x ∷ xs})
