{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Quotient {Σ : Signature} where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.FreeAlgebra

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; Setoid; IsEquivalence; _⇒_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ₁ ℓ₂ ℓ₃ : Level

module _ (S : Algebra Σ {a} {ℓ₁}) where

  open Algebra S using (⟦_⟧; ⟦⟧-cong; _≈_) renaming (Carrier to A)

  private
    setoid : (_▲_ : Rel A ℓ₂) → IsEquivalence _▲_ → Setoid _ _
    setoid _▲_ isEquivalence = record { Carrier       = A
                                      ; _≈_           = _▲_
                                      ; isEquivalence = isEquivalence
                                      }

  record CompatibleEquivalence : Set (a ⊔ ℓ₁ ⊔ suc ℓ₂) where
    field
      _▲_           : Rel A ℓ₂
      isEquivalence : IsEquivalence _▲_
      compatible    : Congruence Σ (setoid _▲_ isEquivalence) ⟦_⟧

    open IsEquivalence isEquivalence public

    ▲-setoid = setoid _▲_ isEquivalence

  underlyingEquivalence : CompatibleEquivalence
  underlyingEquivalence = record { _▲_           = _≈_
                                 ; isEquivalence = Algebra.isEquivalence S
                                 ; compatible    = ⟦⟧-cong
                                 }

_/_-isAlgebra : (S : Algebra Σ {a} {ℓ₁})
                → (▲ : CompatibleEquivalence S {ℓ₂})
                → IsAlgebra Σ (CompatibleEquivalence.▲-setoid ▲)
S / ▲ -isAlgebra = record { ⟦_⟧     = ⟦_⟧
                          ; ⟦⟧-cong = compatible
                          }
  where open Algebra S
        open CompatibleEquivalence ▲

_/_ : (S : Algebra Σ {a} {ℓ₁})
      → CompatibleEquivalence S
      → Algebra Σ {a} {ℓ₂}
S / ▲ = record { Carrierₛ  = ▲-setoid
               ; isAlgebra = S / ▲ -isAlgebra
               }
  where open CompatibleEquivalence ▲

_⊂_ : ∀ {S : Algebra Σ {a} {ℓ₁}}
      → (≈ : CompatibleEquivalence S {ℓ₂})
      → (▲ : CompatibleEquivalence S {ℓ₃})
      → Set _
≈ ⊂ ▲ = (CompatibleEquivalence._▲_ ≈) ⇒ (CompatibleEquivalence._▲_ ▲)

module _ {n}
  {S : Algebra Σ {a} {ℓ₁}}
  {θ : Environment n S}
  {▲ : CompatibleEquivalence S {ℓ₂}}
  where

  open Algebra S using (⟦_⟧)

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ n ⦊) using (Expr; term)
  open import Data.Vec using (Vec; []; _∷_)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using ([]; _∷_)

  mutual
    quotient-subst-args : ∀ {arity}
                          → (xs : Vec Expr arity)
                          → PW.Pointwise _≡_ (subst-args S θ xs) (subst-args (S / ▲) θ xs)
    quotient-subst-args []       = []
    quotient-subst-args (x ∷ xs) = (quotient-subst x) ∷ (quotient-subst-args xs)

    quotient-subst : ∀ (x : Expr) → subst S θ x ≡ subst (S / ▲) θ x
    quotient-subst (term (inj₂ k) []) = PE.refl
    quotient-subst (term (inj₁ f) []) = PE.refl
    quotient-subst (term f (x ∷ xs))  =
      PE.cong ⟦ f ⟧ (PW.Pointwise-≡⇒≡ (quotient-subst-args (x ∷ xs)))
