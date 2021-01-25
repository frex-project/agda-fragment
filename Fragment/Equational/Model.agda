{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Model where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Signature
open import Fragment.Equational.Theory

open import Level using (Level; _⊔_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

Environment : {Σ : Signature} → ℕ → Algebra Σ {a} {ℓ} → Set a
Environment n S = Fin n → Algebra.Carrier S

module _ {Σ n}
  (S : Algebra Σ {a} {ℓ})
  (θ : Environment n S)
  where

  open Algebra S renaming (Carrier to A)

  open import Fragment.Algebra.Homomorphism Σ
  open import Fragment.Algebra.Homomorphism.Setoid Σ using (_≡ₕ_)
  open import Fragment.Algebra.TermAlgebra (Σ ⦉ n ⦊) using (Expr; term)
  open import Fragment.Algebra.TermAlgebra.Extensions

  open import Relation.Binary.Reasoning.Setoid Carrierₛ
  open import Data.Vec.Relation.Binary.Equality.Setoid Carrierₛ using (_≋_)

  Substitution : (Expr → A) → Set a
  Substitution f = ∀ {k : Fin n}
                   → f (term (inj₂ k) []) ≡ θ k

  Substitutionₕ : (|T| Σ ⦉ n ⦊) →ₕ S → Set a
  Substitutionₕ F = Substitution (_→ₕ_.h F)

  mutual
    subst-args : ∀ {arity} → Vec Expr arity → Vec A arity
    subst-args []       = []
    subst-args (x ∷ xs) = (subst x) ∷ (subst-args xs)

    subst : Expr → A
    subst (term (inj₂ k) []) = θ k
    subst (term (inj₁ f) []) = ⟦ f ⟧ []
    subst (term f (x ∷ xs))  = ⟦ f ⟧ (subst-args (x ∷ xs))

  subst-args≡map : ∀ {arity} {xs : Vec Expr arity}
                   → map subst xs ≡ subst-args xs
  subst-args≡map {_} {[]}     = PE.refl
  subst-args≡map {_} {x ∷ xs} = PE.cong (subst x ∷_) (subst-args≡map {_} {xs})

  subst-cong : Congruent _≡_ _≈_ subst
  subst-cong x≡y = reflexive (PE.cong subst x≡y)

  subst-hom : Homomorphic (|T| Σ ⦉ n ⦊) S subst
  subst-hom f xs = ?

  substₕ : (|T| Σ ⦉ n ⦊) →ₕ S
  substₕ = record { h      = subst
                  ; h-cong = subst-cong
                  ; h-hom  = subst-hom
                  }

  subst-subst : Substitution subst
  subst-subst = PE.refl

  substₕ-subst : Substitutionₕ substₕ
  substₕ-subst = subst-subst

_⊨⟨_⟩_ : ∀ {n Σ}
         → (S : Algebra Σ {a} {ℓ})
         → Environment n S
         → Eq Σ n
         → Set ℓ
S ⊨⟨ θ ⟩ (lhs , rhs) = subst S θ lhs ≈ subst S θ rhs
  where open Algebra S using (_≈_)

_⊨_ : ∀ {n Σ}
      → (Algebra Σ {a} {ℓ})
      → Eq Σ n
      → Set (a ⊔ ℓ)
_⊨_ S eq = ∀ {θ} → S ⊨⟨ θ ⟩ eq
