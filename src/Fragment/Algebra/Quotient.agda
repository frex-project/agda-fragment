{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Quotient (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level; Setω; _⊔_; suc)
open import Data.Vec.Properties using (map-id)
open import Relation.Binary using (Setoid; IsEquivalence; Rel)
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

module _
  (A : Algebra {a} {ℓ₁})
  (_≈_ : Rel ∥ A ∥ ℓ₂)
  where

  private
    setoid' : IsEquivalence _≈_ → Setoid _ _
    setoid' isEquivalence =
      record { Carrier       = ∥ A ∥
             ; _≈_           = _≈_
             ; isEquivalence = isEquivalence
             }

  record IsDenominator : Set (a ⊔ suc ℓ₁ ⊔ suc ℓ₂) where
    field
      isEquivalence : IsEquivalence _≈_
      isCoarser     : ∀ {x y} → x =[ A ] y → x ≈ y
      isCompatible  : Congruence (setoid' isEquivalence) (A ⟦_⟧_)

module _
  (A : Algebra {a} {ℓ₁})
  (_≈_ : Rel ∥ A ∥ ℓ₄)
  {{isDenom : IsDenominator A _≈_}}
  where

  record IsQuotient (A/≈ : Algebra {b} {ℓ₂}) : Setω where
    field
      inc : A ⟿ A/≈

      factor : ∀ {c ℓ₃} {X : Algebra {c} {ℓ₃}}
               → (f : A ⟿ X)
               → (Congruent _≈_ ≈[ X ] ∣ f ∣)
               → A/≈ ⟿ X

      commute : ∀ {c ℓ₃} {X : Algebra {c} {ℓ₃}}
               → (f : A ⟿ X)
               → (cong : Congruent _≈_ ≈[ X ] ∣ f ∣)
               → factor f cong ⊙ inc ≗ f

      universal : ∀ {c ℓ₃} {X : Algebra {c} {ℓ₃}}
                  → (f : A ⟿ X)
                  → (cong : Congruent _≈_ ≈[ X ] ∣ f ∣)
                  → {h : A/≈ ⟿ X}
                  → h ⊙ inc ≗ f
                  → factor f cong ≗ h

  open IsDenominator isDenom

  ∥_∥/_ : Setoid _ _
  ∥_∥/_ = record { Carrier       = ∥ A ∥
                 ; _≈_           = _≈_
                 ; isEquivalence = isEquivalence
                 }

  _/_-isAlgebra : IsAlgebra ∥_∥/_
  _/_-isAlgebra = record { ⟦_⟧     = A ⟦_⟧_
                         ; ⟦⟧-cong = isCompatible
                         }

  _/_ : Algebra
  _/_ = record { ∥_∥/≈           = ∥_∥/_
               ; ∥_∥/≈-isAlgebra = _/_-isAlgebra
               }

  ∣inc∣⃗ : ∥ A ∥/≈ ↝ ∥_∥/_
  ∣inc∣⃗ = record { ∣_∣      = λ x → x
                  ; ∣_∣-cong = isCoarser
                  }

  ∣inc∣-hom : Homomorphic A _/_ (λ x → x)
  ∣inc∣-hom f xs =
    Setoid.reflexive ∥_∥/_ (PE.cong (A ⟦ f ⟧_) (map-id xs))

  inc : A ⟿ _/_
  inc = record { ∣_∣⃗    = ∣inc∣⃗
               ; ∣_∣-hom = ∣inc∣-hom
               }

  module _ {c ℓ₃}
    {X : Algebra {c} {ℓ₃}}
    (f : A ⟿ X)
    (cong : Congruent _≈_ ≈[ X ] ∣ f ∣)
    where

    ∣factor∣⃗ : ∥_∥/_ ↝ ∥ X ∥/≈
    ∣factor∣⃗ = record { ∣_∣      = ∣ f ∣
                       ; ∣_∣-cong = cong
                       }

    factor : _/_ ⟿ X
    factor = record { ∣_∣⃗    = ∣factor∣⃗
                    ; ∣_∣-hom = ∣ f ∣-hom
                    }

    factor-commute : factor ⊙ inc ≗ f
    factor-commute = Setoid.refl ∥ X ∥/≈

    factor-universal : ∀ {h : _/_ ⟿ X} → h ⊙ inc ≗ f → factor ≗ h
    factor-universal p {x} = sym (p {x})
      where open Setoid ∥ X ∥/≈

  _/_-isQuotient : IsQuotient (_/_)
  _/_-isQuotient = record { inc       = inc
                          ; factor    = factor
                          ; commute   = factor-commute
                          ; universal = factor-universal
                          }
