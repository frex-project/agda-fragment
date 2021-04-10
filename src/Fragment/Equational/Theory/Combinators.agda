{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory.Combinators where

open import Fragment.Equational.Theory.Base

open import Fragment.Algebra.Signature
open import Fragment.Algebra.TermAlgebra
open import Fragment.Algebra.FreeAlgebra

open import Function using (_∘_)

open import Data.Nat using (ℕ)
open import Data.Fin using (#_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_,_)

private
  mutual
    extend-expr-args : ∀ {Σ n m arity}
                       → Vec (Expr (Σ ⦉ m ⦊)) arity
                       → Vec (Expr ((Σ ⦉ n ⦊) ⦉ m ⦊)) arity
    extend-expr-args []       = []
    extend-expr-args (x ∷ xs) = extend-expr x ∷ extend-expr-args xs

    extend-expr : ∀ {Σ n m}
                  → Expr (Σ ⦉ m ⦊)
                  → Expr ((Σ ⦉ n ⦊) ⦉ m ⦊)
    extend-expr (term₂ k)         = term₂ k
    extend-expr (term₁ f)         = term₁ (inj₁ f)
    extend-expr (term f (x ∷ xs)) = term f (extend-expr-args (x ∷ xs))

  extend : ∀ {Σ n arity}
           → Eq Σ arity
           → Eq (Σ ⦉ n ⦊) arity
  extend (lhs , rhs) = extend-expr lhs , extend-expr rhs

_⦉_⦊ₜ : (Θ : Theory) → ℕ → Theory
Θ ⦉ n ⦊ₜ = record { Σ     = (Σ Θ) ⦉ n ⦊
                  ; eqs   = eqs Θ
                  ; _⟦_⟧ₑ = extend ∘ (Θ ⟦_⟧ₑ)
                  }

module _ (Θ : Theory) where

  import Fragment.Equational.Theory.Laws ((Σ Θ) ⦉ 1 ⦊) as L

  data WithIdEq : ℕ → Set where
    idₗ       : WithIdEq 1
    idᵣ       : WithIdEq 1
    inherited : ∀ {n} → eqs Θ n → WithIdEq n

  AddId : (ops (Σ Θ) 2) → Theory
  AddId • = record { Σ     = (Σ Θ) ⦉ 1 ⦊
                   ; eqs   = WithIdEq
                   ; _⟦_⟧ₑ = withId
                   }
    where withId : ∀ {arity} → WithIdEq arity → Eq ((Σ Θ) ⦉ 1 ⦊) arity
          withId idₗ           = L.idₗ (inj₂ (# 0)) •
          withId idᵣ           = L.idᵣ (inj₂ (# 0)) •
          withId (inherited e) = extend (Θ ⟦ e ⟧ₑ)
