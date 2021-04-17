{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Evaluation (Σ : Signature) where

open import Fragment.Algebra.Free.Monad Σ
open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Free.Base Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Setoid.Morphism as Morphism

open import Level using (Level)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as PE

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
    ∣eval∣-cong {x = term op _} (term p) =
      (A ⟦ op ⟧-cong) (∣eval∣-args-cong p)

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
fold B f = (eval B) ⊙ bind (unit · f)

Env : (A : Algebra {a} {ℓ₁}) → ℕ → Set _
Env A n = Fin n → ∥ A ∥

∣inst∣-args : ∀ {n m} (A : Algebra {a} {ℓ₁})
              → Env A n
              → Vec ∥ F n ∥ m
              → Vec ∥ A ∥ m
∣inst∣-args A θ xs =
  ∣eval∣-args A (∣bind∣-args Morphism.∣ unit · (lift {B = ∥ A ∥/≈} θ) ∣ xs)

inst : ∀ {n} (A : Algebra {a} {ℓ₁})
       → Env A n → F n ⟿ A
inst A θ = fold A (lift θ)

{-
subst : ∀ {n} (A : Algebra {a} {ℓ₁})
        → Env A n → Adjoin A n ⟿ A
subst {n = n} A θ = fold A sub
  where ∣sub∣ : BT ∥ A ∥ n → ∥ A ∥
        ∣sub∣ (sta x) = x
        ∣sub∣ (dyn n) = θ n

        ∣sub∣-cong : ∀ {x y} → x ≑ y → ∣sub∣ x =[ A ] ∣sub∣ y
        ∣sub∣-cong (sta x≈y) = x≈y
        ∣sub∣-cong (dyn x≡y) = Setoid.reflexive ∥ A ∥/≈ (PE.cong θ x≡y)

        sub : Atoms ∥ A ∥/≈ n ↝ ∥ A ∥/≈
        sub = record { ∣_∣      = ∣sub∣
                     ; ∣_∣-cong = ∣sub∣-cong
                     }
-}
