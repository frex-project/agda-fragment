{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.TermAlgebra.Properties (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.TermAlgebra.Base Σ
open import Fragment.Algebra.Initial Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ using (_≡ₕ_)

open import Level using (Level)
open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)
open import Data.Vec using (Vec; []; _∷_; map)

private
  variable
    a ℓ : Level

module _ (S : Algebra {a} {ℓ}) where

  open Setoid ∥ S ∥/≈

  open import Relation.Binary.Reasoning.Setoid ∥ S ∥/≈
  open import Data.Vec.Relation.Binary.Equality.Setoid ∥ S ∥/≈ using (_≋_)

  mutual
    eval-args : ∀ {arity} → Vec Expr arity → Vec ∥ S ∥ arity
    eval-args []       = []
    eval-args (x ∷ xs) = (eval x) ∷ (eval-args xs)

    eval : Expr → ∥ S ∥
    eval (term f xs) = (S ⟦ f ⟧) (eval-args xs)

  eval-args≡map : ∀ {arity} {xs : Vec Expr arity}
                  → map eval xs ≡ eval-args xs
  eval-args≡map {_} {[]}     = PE.refl
  eval-args≡map {_} {x ∷ xs} = PE.cong (eval x ∷_) (eval-args≡map {_} {xs})

  eval-cong : Congruent _≡_ _≈_ eval
  eval-cong x≡y = reflexive (PE.cong eval x≡y)

  eval-hom : Homomorphic |T| S eval
  eval-hom f xs = reflexive (PE.cong (S ⟦ f ⟧) (eval-args≡map {_} {xs}))

  evalₕ : |T| →ₕ S
  evalₕ = record { ∥_∥ₕ      = eval
                 ; ∥_∥ₕ-cong = eval-cong
                 ; ∥_∥ₕ-hom  = eval-hom
                 }

  mutual
    eval-args-universal : (h : |T| →ₕ S)
                          → ∀ {arity} {xs : Vec Expr arity}
                          → map ∥ h ∥ₕ xs ≋ eval-args xs
    eval-args-universal _ {_} {[]}     = []
    eval-args-universal h {_} {x ∷ xs} =
      evalₕ-universal h {x} ∷ eval-args-universal h {_} {xs}

    evalₕ-universal : (h : |T| →ₕ S) → h ≡ₕ evalₕ
    evalₕ-universal h {term f xs} = begin
        ∥ h ∥ₕ (term f xs)
      ≈⟨ sym (∥ h ∥ₕ-hom f xs) ⟩
        (S ⟦ f ⟧) (map ∥ h ∥ₕ xs)
      ≈⟨ (S ⟦⟧-cong) f (eval-args-universal h) ⟩
        (S ⟦ f ⟧) (eval-args xs)
      ∎

|T|-isInitial : IsInitial |T|
|T|-isInitial = record { []_       = evalₕ
                       ; universal = λ {_} {_} {S} → evalₕ-universal S
                       }
