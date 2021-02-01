{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Quotient {Σ : Signature} where

open import Fragment.Algebra.Algebra

open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

private
  variable
    a ℓ₁ ℓ₂ : Level

module _ (S : Algebra Σ {a} {ℓ₁}) where

  open Algebra S using (⟦_⟧; _≈_) renaming (Carrier to A)

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
