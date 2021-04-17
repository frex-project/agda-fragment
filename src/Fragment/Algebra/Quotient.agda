{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Quotient (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level; _⊔_; suc)

open import Relation.Binary using (Rel; Setoid; IsEquivalence; _⇒_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Data.Vec using (Vec; []; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using ([]; _∷_; Pointwise-≡⇒≡; Pointwise)

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ : Level

module _ (A : Algebra {a} {ℓ₁}) where

  private
    setoid' : (_≈_ : Rel ∥ A ∥ ℓ₂) → IsEquivalence _≈_ → Setoid _ _
    setoid' _≈_ isEquivalence =
      record { Carrier       = ∥ A ∥
             ; _≈_           = _≈_
             ; isEquivalence = isEquivalence
             }

  record CompatibleEquivalence : Set (a ⊔ ℓ₁ ⊔ suc ℓ₂) where
    field
      _≈_           : Rel ∥ A ∥ ℓ₂
      isEquivalence : IsEquivalence _≈_
      compatible    : Congruence (setoid' _≈_ isEquivalence) (A ⟦_⟧_)

    open IsEquivalence isEquivalence public

    setoid : Setoid a ℓ₂
    setoid = setoid' _≈_ isEquivalence

  underlying : CompatibleEquivalence
  underlying = record { _≈_           = ≈[ A ]
                      ; isEquivalence = ≈[ A ]-isEquivalence
                      ; compatible    = A ⟦_⟧-cong
                      }

open CompatibleEquivalence using (setoid; compatible) public

_/_-isAlgebra : (A : Algebra {a} {ℓ₁})
                → (≈ : CompatibleEquivalence A {ℓ₂})
                → IsAlgebra (setoid ≈)
A / ≈ -isAlgebra = record { ⟦_⟧     = A ⟦_⟧_
                          ; ⟦⟧-cong = compatible ≈
                          }

_/_ : (A : Algebra {a} {ℓ₁})
    → CompatibleEquivalence A
    → Algebra {a} {ℓ₂}
A / ≈ = record { ∥_∥/≈           = setoid ≈
               ; ∥_∥/≈-isAlgebra = A / ≈ -isAlgebra
               }
