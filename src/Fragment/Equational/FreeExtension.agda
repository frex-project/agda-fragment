{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension (Θ : Theory) where

open import Fragment.Equational.FreeExtension.Base Θ public
open import Fragment.Equational.FreeExtension.Synthetic Θ public
open import Fragment.Equational.FreeExtension.Properties Θ public

{-
module _
  (X : FreeExtension)
  (A : Model {a} {ℓ})
  (n : ℕ)
  where

  open FreeExtension X

  open IsCoproduct (A [ n ]-isFrex)

  open module T = Setoid ∥ A ∥/≈
  open Setoid ∥ A [ n ] ∥/≈ renaming (_≈_ to _≋_) using ()
  open Setoid ∥ Adjoinₘ A n ∥/≈ renaming (_≈_ to _≊_) using ()

  norm : ∥ Adjoinₘ A n ∥ₐ ⟿ ∥ A [ n ] ∥ₐ
  norm = {!!} -- fold ∥ A [ n ] ∥ₐ sub
    where ∣sub∣ : BT ∥ A ∥ n → ∥ A [ n ] ∥
          ∣sub∣ (sta x) = ∣ inl ∣ x
          ∣sub∣ (dyn n) = ∣ inr ∣ (atom n)

          ∣sub∣-cong : ∀ {x y} → _≑_ ∥ A ∥/≈ n x y → ∣sub∣ x ≋ ∣sub∣ y
          ∣sub∣-cong (sta x≈y) = ∣ inl ∣-cong x≈y
          ∣sub∣-cong (dyn x≡y) =
            ∣ inr ∣-cong (Setoid.reflexive ∥ Finₘ n ∥/≈ (PE.cong atom x≡y))

          sub : ∥ Adjoinₘ A n ∥/≈ ↝ ∥ A [ n ] ∥/≈
          sub = ∣ {!bind!} ∣⃗

  iso : ∥ A [ n ] ∥ₐ ≃ ∥ Adjoinₘ A n ∥ₐ
  iso = record { _⃗   = (Adjoinₘ A n) [ {!!} , {!!} ]
               ; _⃖   = norm
               ; invˡ = {!!}
               ; invʳ = {!!}
               }

  fundamental : ∀ (θ : Env ∥ A ∥ₐ n)
                → A [ id , interp A θ ] ⊙ norm ≗ {!!}
  fundamental θ = {!!}

  frexify : ∀ {lhs rhs : Term (BT ∥ A ∥ n)}
            → (θ : Env ∥ A ∥ₐ n)
            → ∣ norm ∣ lhs ≋ ∣ norm ∣ rhs
            → ∣ subst ∥ A ∥ₐ θ ∣ lhs ≈ ∣ subst ∥ A ∥ₐ θ ∣ rhs
  frexify {lhs = lhs} {rhs = rhs} θ p = begin
      ∣ subst ∥ A ∥ₐ θ ∣ lhs
    ≈⟨ T.sym (fundamental θ {x = lhs}) ⟩
      ∣ A [ id , interp A θ ] ⊙ norm ∣ lhs
    ≈⟨ ∣ A [ id , interp A θ ] ∣-cong p ⟩
      ∣ A [ id , interp A θ ] ⊙ norm ∣ rhs
    ≈⟨ fundamental θ {x = rhs} ⟩
      ∣ subst ∥ A ∥ₐ θ ∣ rhs
    ∎
    where open import Relation.Binary.Reasoning.Setoid ∥ A ∥/≈
-}
