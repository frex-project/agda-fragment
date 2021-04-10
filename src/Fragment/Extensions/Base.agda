{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.Base where

open import Level using (Level; _⊔_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

data BT (n : ℕ) (A : Set a) : Set a where
  sta : A → BT n A
  dyn : Fin n → BT n A

module _ (n : ℕ) (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  data _≈BT_ : BT n A → BT n A → Set (a ⊔ ℓ) where
    ≈-sta : ∀ {x y} → x ≈ y → sta x ≈BT sta y
    ≡-dyn : ∀ {x y} → x ≡ y → dyn x ≈BT dyn y

  ≈BT-refl : ∀ {x} → x ≈BT x
  ≈BT-refl {sta x} = ≈-sta refl
  ≈BT-refl {dyn x} = ≡-dyn PE.refl

  ≈BT-sym : ∀ {x y} → x ≈BT y → y ≈BT x
  ≈BT-sym (≈-sta p) = ≈-sta (sym p)
  ≈BT-sym (≡-dyn p) = ≡-dyn (PE.sym p)

  ≈BT-trans : ∀ {x y z} → x ≈BT y → y ≈BT z → x ≈BT z
  ≈BT-trans (≈-sta p) (≈-sta q) = ≈-sta (trans p q)
  ≈BT-trans (≡-dyn p) (≡-dyn q) = ≡-dyn (PE.trans p q)

  ≈BT-isEquivalence : IsEquivalence _≈BT_
  ≈BT-isEquivalence = record { refl  = ≈BT-refl
                             ; sym   = ≈BT-sym
                             ; trans = ≈BT-trans
                             }

  ≈BT-setoid : Setoid a (a ⊔ ℓ)
  ≈BT-setoid = record { Carrier       = BT n A
                      ; _≈_           = _≈BT_
                      ; isEquivalence = ≈BT-isEquivalence
                      }
