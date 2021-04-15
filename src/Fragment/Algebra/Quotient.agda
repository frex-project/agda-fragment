{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Quotient (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ

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

module _ (S : Algebra {a} {ℓ₁}) where

  private
    setoid' : (_≈_ : Rel ∥ S ∥ ℓ₂) → IsEquivalence _≈_ → Setoid _ _
    setoid' _≈_ isEquivalence = record { Carrier       = ∥ S ∥
                                       ; _≈_           = _≈_
                                       ; isEquivalence = isEquivalence
                                       }

  record CompatibleEquivalence : Set (a ⊔ ℓ₁ ⊔ suc ℓ₂) where
    field
      _≈_           : Rel ∥ S ∥ ℓ₂
      isEquivalence : IsEquivalence _≈_
      compatible    : Congruence (setoid' _≈_ isEquivalence) (S ⟦_⟧_)

    open IsEquivalence isEquivalence public

    setoid : Setoid a ℓ₂
    setoid = setoid' _≈_ isEquivalence

  underlyingEquivalence : CompatibleEquivalence
  underlyingEquivalence = record { _≈_           = ≈[ S ]
                                 ; isEquivalence = ≈[ S ]-isEquivalence
                                 ; compatible    = S ⟦_⟧-cong
                                 }

open CompatibleEquivalence using (setoid; compatible)

_/_-isAlgebra : (S : Algebra {a} {ℓ₁})
                → (≈ : CompatibleEquivalence S {ℓ₂})
                → IsAlgebra (setoid ≈)
S / ≈ -isAlgebra = record { ⟦_⟧     = S ⟦_⟧_
                          ; ⟦⟧-cong = compatible ≈
                          }

_/_ : (S : Algebra {a} {ℓ₁})
    → CompatibleEquivalence S
    → Algebra {a} {ℓ₂}
S / ≈ = record { ∥_∥/≈           = setoid ≈
               ; ∥_∥/≈-isAlgebra = S / ≈ -isAlgebra
               }
