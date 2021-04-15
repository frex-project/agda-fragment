{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Evaluation (Σ : Signature) where

open import Fragment.Algebra.Free.Monad Σ
open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Free.Base Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Setoid.Morphism

open import Level using (Level)

open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid)

private
  variable
    a b ℓ₁ ℓ₂ : Level

module _ (A : Algebra {a} {ℓ₁}) where

  open Setoid ∥ A ∥/≈
  open import Relation.Binary.Reasoning.Setoid ∥ A ∥/≈

  mutual
    ∣eval∣-args : ∀ {n} → Vec (Term ∥ A ∥) n → Vec ∥ A ∥ n
    ∣eval∣-args []       = []
    ∣eval∣-args (x ∷ xs) = ∣eval∣ x ∷ ∣eval∣-args xs

    ∣eval∣ : Term ∥ A ∥ → ∥ A ∥
    ∣eval∣ (atom x)    = x
    ∣eval∣ (term f xs) = A ⟦ f ⟧ (∣eval∣-args xs)

  mutual
    ∣eval∣-args-cong : ∀ {n} {xs ys : Vec (Term ∥ A ∥) n}
                       → Pointwise (_∼_ ∥ A ∥/≈) xs ys
                       → Pointwise ≈[ A ] (∣eval∣-args xs)
                                          (∣eval∣-args ys)
    ∣eval∣-args-cong []       = []
    ∣eval∣-args-cong (p ∷ ps) = ∣eval∣-cong p ∷ ∣eval∣-args-cong ps

    ∣eval∣-cong : Congruent (_∼_ ∥ A ∥/≈) ≈[ A ] ∣eval∣
    ∣eval∣-cong (atom p)                 = p
    ∣eval∣-cong {x = term op _} (term p) = (A ⟦ op ⟧-cong) (∣eval∣-args-cong p)

  ∣eval∣⃗ : Herbrand ∥ A ∥/≈ ↝ ∥ A ∥/≈
  ∣eval∣⃗ = record { ∣_∣      = ∣eval∣
                   ; ∣_∣-cong = ∣eval∣-cong
                   }

  ∣eval∣-args≡map : ∀ {n} {xs : Vec (Term ∥ A ∥) n}
                    → Pointwise _≈_ (∣eval∣-args xs) (map ∣eval∣ xs)
  ∣eval∣-args≡map {xs = []}     = []
  ∣eval∣-args≡map {xs = x ∷ xs} = refl ∷ ∣eval∣-args≡map

  ∣eval∣-hom : Homomorphic (Free ∥ A ∥/≈) A ∣eval∣
  ∣eval∣-hom f []       = refl
  ∣eval∣-hom f (x ∷ xs) = sym ((A ⟦ f ⟧-cong) (∣eval∣-args≡map {xs = x ∷ xs}))

  eval : Free ∥ A ∥/≈ ⟿ A
  eval = record { ∣_∣⃗    = ∣eval∣⃗
                ; ∣_∣-hom = ∣eval∣-hom
                }

fold : ∀ {A : Setoid a ℓ₁} (B : Algebra {b} {ℓ₂})
       → (A ↝ ∥ B ∥/≈) → Free A ⟿ B
fold B θ = (eval B) ⊙ bind (unit · θ)
