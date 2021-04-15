{-# OPTIONS --without-K --safe #-}

module Fragment.Setoid.Morphism.Base where

open import Level using (Level; _⊔_)
open import Function using (_∘_; Congruent)

import Relation.Binary.PropositionalEquality as PE
open import Relation.Binary using (Setoid)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where

  open Setoid S renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid T renaming (Carrier to B; _≈_ to _≈₂_)

  infixr 1 _↝_

  record _↝_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ∣_∣      : A → B
      ∣_∣-cong : Congruent _≈₁_ _≈₂_ ∣_∣

open _↝_ public

lift : ∀ {A : Set a} {B : Setoid b ℓ₂}
       → (A → Setoid.Carrier B)
       → (PE.setoid A ↝ B)
lift {B = B} f
  = record { ∣_∣ = f
           ; ∣_∣-cong = reflexive ∘ (PE.cong f)
           }
     where open Setoid B

id : ∀ {A : Setoid a ℓ₁} → A ↝ A
id = record { ∣_∣ = λ x → x ; ∣_∣-cong = λ x → x }

_·_ : ∀ {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} {C : Setoid c ℓ₃}
      → B ↝ C → A ↝ B → A ↝ C
g · f = record { ∣_∣      = ∣ g ∣ ∘ ∣ f ∣
               ; ∣_∣-cong = ∣ g ∣-cong ∘ ∣ f ∣-cong
               }
