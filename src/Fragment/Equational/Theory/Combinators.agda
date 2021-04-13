{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory.Combinators where

open import Fragment.Equational.Theory.Base
open import Fragment.Equational.Satisfaction

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Combinators
open import Fragment.Algebra.Algebra using (Algebra)
open import Fragment.Algebra.TermAlgebra
open import Fragment.Algebra.FreeAlgebra

open import Level using (Level)
open import Function using (_∘_)
open import Function.Bundles using (Inverse)

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; #_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; Pointwise-≡⇒≡; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Product.Properties using (×-≡,≡↔≡)

open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

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

mutual
  subst-args-⊨ : ∀ {Σ n m arity} {A : Algebra (Σ ⦉ n ⦊) {a} {ℓ}}
                 → (xs : Vec (Expr (Σ ⦉ m ⦊)) arity)
                 → (θ : Environment Σ m (forget A))
                 → Pointwise _≡_
                    (subst-args (Σ ⦉ n ⦊) A θ (extend-expr-args xs))
                    (subst-args Σ (forget A) θ xs)
  subst-args-⊨ [] _       = []
  subst-args-⊨ (x ∷ xs) θ = subst-⊨ x θ ∷ subst-args-⊨ xs θ

  subst-⊨ : ∀ {Σ n m} {A : Algebra (Σ ⦉ n ⦊) {a} {ℓ}}
             → (x : Expr (Σ ⦉ m ⦊)) → (θ : Environment Σ m (forget A))
             → subst (Σ ⦉ n ⦊) A θ (extend-expr x) ≡ subst Σ (forget A) θ x
  subst-⊨ (term₁ f) θ = PE.refl
  subst-⊨ (term₂ k) θ = PE.refl
  subst-⊨ {A = A} (term f (x ∷ xs)) θ =
    PE.cong (A ⟦ f ⟧) (Pointwise-≡⇒≡ (subst-args-⊨ (x ∷ xs) θ))
    where open import Fragment.Algebra.Algebra

forget-⊨ : ∀ {Σ n arity} {A : Algebra (Σ ⦉ n ⦊) {a} {ℓ}}
           → {eq : Eq Σ arity}
           → A ⊨ extend eq
           → forget A ⊨ eq
forget-⊨ {Σ = Σ} {n = n} {A = A} {eq = lhs , rhs} x {θ} = begin
    subst Σ (forget A) θ lhs
  ≈⟨ A.sym (A.reflexive (subst-⊨ lhs θ)) ⟩
    subst (Σ ⦉ n ⦊) A θ (extend-expr lhs)
  ≈⟨ x ⟩
    subst (Σ ⦉ n ⦊) A θ (extend-expr rhs)
  ≈⟨ A.reflexive (subst-⊨ rhs θ) ⟩
    subst Σ (forget A) θ rhs
  ∎
  where open import Fragment.Algebra.Algebra
        open module A = Setoid ∥ A ∥/≈
        open import Relation.Binary.Reasoning.Setoid ∥ A ∥/≈

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
