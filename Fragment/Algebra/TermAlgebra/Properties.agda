{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.TermAlgebra.Properties (Σ : Signature) where

open import Fragment.Algebra.Algebra

open import Fragment.Algebra.TermAlgebra.Base Σ
open import Fragment.Algebra.Initial Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ using (_≡ₕ_)

open import Level using (Level)

open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Data.Vec using (Vec; []; _∷_; map)

private
  variable
    a ℓ : Level

module _ (S : Algebra Σ {a} {ℓ}) where

  open Algebra S renaming (Carrier to A)
  
  open import Relation.Binary.Reasoning.Setoid Carrierₛ
  open import Data.Vec.Relation.Binary.Equality.Setoid Carrierₛ using (_≋_)

  mutual
    eval-args : ∀ {arity} → Vec Expr arity → Vec A arity
    eval-args []       = []
    eval-args (x ∷ xs) = (eval x) ∷ (eval-args xs)

    eval : Expr → A
    eval (term f xs) = ⟦ f ⟧ (eval-args xs)

  eval-args≡map : ∀ {arity} {xs : Vec Expr arity}
                  → map eval xs ≡ eval-args xs
  eval-args≡map {_} {[]}     = PE.refl
  eval-args≡map {_} {x ∷ xs} = PE.cong (eval x ∷_) (eval-args≡map {_} {xs})

  eval-cong : Congruent _≡_ _≈_ eval
  eval-cong x≡y = reflexive (PE.cong eval x≡y)

  eval-hom : Homomorphic |T| S eval
  eval-hom f xs = reflexive (PE.cong ⟦ f ⟧ (eval-args≡map {_} {xs}))

  evalₕ : |T| →ₕ S
  evalₕ = record { h      = eval
                 ; h-cong = eval-cong
                 ; h-hom  = eval-hom
                 }

  mutual
    eval-args-universal : (H : |T| →ₕ S)
                          → ∀ {arity} {xs : Vec Expr arity}
                          → map (_→ₕ_.h H) xs ≋ eval-args xs
    eval-args-universal H {_} {[]}     = PW.[]
    eval-args-universal H {_} {x ∷ xs} =
      PW._∷_ (evalₕ-universal H {x}) (eval-args-universal H {_} {xs})

    evalₕ-universal : (H : |T| →ₕ S) → H ≡ₕ evalₕ
    evalₕ-universal H {term f xs} = begin
        h (term f xs)
      ≈⟨ sym (h-hom f xs) ⟩
        ⟦ f ⟧ (map h xs)
      ≈⟨ ⟦⟧-cong f (eval-args-universal H) ⟩
        ⟦ f ⟧ (eval-args xs)
      ≡⟨⟩
        eval (term f xs)
      ∎
      where open _→ₕ_ H

|T|-isInitial : IsInitial |T|
|T|-isInitial = record { []_       = evalₕ
                       ; universal = λ {_} {_} {S} → evalₕ-universal S
                       }
