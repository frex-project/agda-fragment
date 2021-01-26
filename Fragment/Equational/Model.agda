{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Model where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Signature
open import Fragment.Equational.Theory

open import Level using (Level; _⊔_)
open import Function using (_$_)

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
open import Data.Vec using (Vec; []; _∷_; map)

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
  open import Data.Vec.Relation.Binary.Equality.Setoid Carrierₛ

  Substitution : (Expr → A) → Set a
  Substitution f = ∀ {k : Fin n}
                   → f (term (inj₂ k) []) ≡ θ k

  Substitutionₕ : (|T| Σ ⦉ n ⦊) →ₕ S → Set a
  Substitutionₕ H = Substitution (_→ₕ_.h H)

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
  subst-hom {_} f []       = refl
  subst-hom {m} f (x ∷ xs) =
    ⟦⟧-cong f $
      IsEquivalence.reflexive
        (≋-isEquivalence m)
        (subst-args≡map {_} {x ∷ xs})

  substₕ : (|T| Σ ⦉ n ⦊) →ₕ S
  substₕ = record { h      = subst
                  ; h-cong = subst-cong
                  ; h-hom  = subst-hom
                  }

  subst-subst : Substitution subst
  subst-subst = PE.refl

  substₕ-subst : Substitutionₕ substₕ
  substₕ-subst = subst-subst

  mutual
    subst-args-universal : (H : (|T| Σ ⦉ n ⦊) →ₕ S)
                           → Substitutionₕ H
                           → ∀ {arity} {xs : Vec Expr arity}
                           → map (_→ₕ_.h H) xs ≋ subst-args xs
    subst-args-universal H _       {_} {[]}     = PW.[]
    subst-args-universal H h-subst {_} {x ∷ xs} =
      PW._∷_
        (substₕ-universal H h-subst {x})
        (subst-args-universal H h-subst {_} {xs})

    substₕ-universal : (H : (|T| Σ ⦉ n ⦊) →ₕ S)
                       → Substitutionₕ H
                       → H ≡ₕ substₕ
    substₕ-universal H h-subst {term (inj₂ k) []} = reflexive (h-subst {k})
    substₕ-universal H _       {term (inj₁ f) []} = sym (h-hom f [])
      where open _→ₕ_ H
    substₕ-universal H h-subst {term f (x ∷ xs)}  = begin
        h (term f (x ∷ xs))
      ≈⟨ sym (h-hom f (x ∷ xs)) ⟩
        ⟦ f ⟧ (map h (x ∷ xs))
      ≈⟨ ⟦⟧-cong f (subst-args-universal H h-subst) ⟩
        ⟦ f ⟧ (subst-args (x ∷ xs))
      ≡⟨⟩
        subst (term f (x ∷ xs))
      ∎
      where open _→ₕ_ H

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
