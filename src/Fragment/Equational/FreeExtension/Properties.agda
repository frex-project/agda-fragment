{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension.Properties (Θ : Theory) where

open import Fragment.Algebra.Algebra (Σ Θ) using (Algebra)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Free (Σ Θ)
open import Fragment.Equational.Model Θ
open import Fragment.Equational.Coproduct Θ
open import Fragment.Equational.FreeExtension.Base Θ
open import Fragment.Equational.FreeExtension.Synthetic Θ using (SynFrex)

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as Reasoning

private
  variable
    a ℓ₁ : Level

module _
  (X : FreeExtension)
  (Y : FreeExtension)
  (A : Model {a} {ℓ₁})
  (n : ℕ)
  where

  open FreeExtension X renaming (_[_] to _[_]₁; _[_]-isFrex to _[_]₁-isFrex)
  open FreeExtension Y renaming (_[_] to _[_]₂; _[_]-isFrex to _[_]₂-isFrex)

  open IsCoproduct (A [ n ]₁-isFrex)
    renaming (inl to inl₁; inr to inr₁; _[_,_] to _[_,_]₁; commute₁ to commute₁₁; commute₂ to commute₂₁)
  open IsCoproduct (A [ n ]₂-isFrex)
    renaming (inl to inl₂; inr to inr₂; _[_,_] to _[_,_]₂; commute₁ to commute₁₂; commute₂ to commute₂₂)
    using ()

  to : ∥ A [ n ]₂ ∥ₐ ⟿ ∥ A [ n ]₁ ∥ₐ
  to = (A [ n ]₁) [ inl₁ , inr₁ ]₂

  from : ∥ A [ n ]₁ ∥ₐ ⟿ ∥ A [ n ]₂ ∥ₐ
  from = (A [ n ]₂) [ inl₂ , inr₂ ]₁

  inv : to ⊙ from ≗ id
  inv = begin
      to ⊙ from
    ≈⟨ ≗-sym {f = (A [ n ]₁) [ inl₁ , inr₁ ]₁} {g = to ⊙ from} (universal {h = to ⊙ from} c₁ c₂) ⟩
      (A [ n ]₁) [ inl₁ , inr₁ ]₁
    ≈⟨ universal {h = id} (id-unitˡ {f = inl₁}) (id-unitˡ {f = inr₁}) ⟩
      id
    ∎
    where c₁ : (to ⊙ from) ⊙ inl₁ ≗ inl₁
          c₁ = begin
              (to ⊙ from) ⊙ inl₁
            ≈⟨ ⊙-assoc to from inl₁ ⟩
              to ⊙ (from ⊙ inl₁)
            ≈⟨ ⊙-congˡ to (from ⊙ inl₁) inl₂ (commute₁₁ {f = inl₂} {g = inr₂}) ⟩
              to ⊙ inl₂
            ≈⟨ commute₁₂ {X = A [ n ]₁} {f = inl₁} {g = inr₁} ⟩
              inl₁
            ∎
            where open Reasoning (∥ A ∥ₐ ⟿ ∥ A [ n ]₁ ∥ₐ /≗)

          c₂ : (to ⊙ from) ⊙ inr₁ ≗ inr₁
          c₂ = begin
              (to ⊙ from) ⊙ inr₁
            ≈⟨ ⊙-assoc to from inr₁ ⟩
              to ⊙ (from ⊙ inr₁)
            ≈⟨ ⊙-congˡ to (from ⊙ inr₁) inr₂ (commute₂₁ {f = inl₂} {g = inr₂}) ⟩
              to ⊙ inr₂
            ≈⟨ commute₂₂ {X = A [ n ]₁} {f = inl₁} {g = inr₁} ⟩
              inr₁
            ∎
            where open Reasoning (∥ J n ∥ₐ ⟿ ∥ A [ n ]₁ ∥ₐ /≗)

          open Reasoning (∥ A [ n ]₁ ∥ₐ ⟿ ∥ A [ n ]₁ ∥ₐ /≗)

module _
  (X : FreeExtension)
  (Y : FreeExtension)
  (A : Model {a} {ℓ₁})
  (n : ℕ)
  where

  open FreeExtension X renaming (_[_] to _[_]₁)
  open FreeExtension Y renaming (_[_] to _[_]₂)

  iso : ∥ A [ n ]₁ ∥ₐ ≃ ∥ A [ n ]₂ ∥ₐ
  iso = record { _⃗   = to Y X A n
               ; _⃖   = from Y X A n
               ; invˡ = inv Y X A n
               ; invʳ = inv X Y A n
               }

module _
  (X : FreeExtension)
  (A : Model {a} {ℓ₁})
  {n : ℕ}
  where

  open FreeExtension X
  open FreeExtension SynFrex renaming (_[_] to _[_]ₛ; _[_]-isFrex to _[_]ₛ-isFrex)

  open IsCoproduct (A [ n ]-isFrex)
  open IsCoproduct (A [ n ]ₛ-isFrex) renaming (_[_,_] to _[_,_]ₛ) using ()

  open Setoid ∥ A [ n ] ∥/≈ renaming (_≈_ to _≋_)
  open Setoid ∥ A ∥/≈ using (_≈_)

  norm = to X SynFrex A n
  syn = from X SynFrex A n

  reduce : (θ : Env ∥ A ∥ₐ n) → ∥ A [ n ]ₛ ∥ₐ ⟿ ∥ A ∥ₐ
  reduce θ = A [ id , interp A θ ]ₛ

  module _ (Γ : Vec ∥ A ∥ n) where

    private

      θ : Env ∥ A ∥ₐ n
      θ = env {A = ∥ A ∥ₐ} Γ

    frexify : ∀ {lhs rhs : Term (BT ∥ A ∥ n)}
              → ∣ norm ∣ lhs ≋ ∣ norm ∣ rhs
              → ∣ reduce θ ∣ lhs ≈ ∣ reduce θ ∣ rhs
    frexify {lhs = lhs} {rhs = rhs} p = begin
        ∣ reduce θ ∣ lhs
      ≈⟨ Setoid.sym ∥ A ∥/≈ (∣ reduce θ ∣-cong (inv SynFrex X A n {x = lhs})) ⟩
        ∣ reduce θ ∣ (∣ syn ∣ (∣ norm ∣ lhs))
      ≈⟨ ∣ reduce θ ∣-cong (∣ syn ∣-cong p) ⟩
        ∣ reduce θ ∣ (∣ syn ∣ (∣ norm ∣ rhs))
      ≈⟨ ∣ reduce θ ∣-cong (inv SynFrex X A n {x = rhs}) ⟩
        ∣ reduce θ ∣ rhs
      ∎
      where open Reasoning ∥ A ∥/≈
