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

∣fold∣-args : ∀ {m} {A : Setoid a ℓ₁} (B : Algebra {b} {ℓ₂})
              → (A ↝ ∥ B ∥/≈) → Vec ∥ Free A ∥ m → Vec ∥ B ∥ m
∣fold∣-args B f xs =
  ∣eval∣-args B (∣bind∣-args Morphism.∣ unit · f ∣ xs)

Env : (A : Algebra {a} {ℓ₁}) → ℕ → Set _
Env A n = Fin n → ∥ A ∥

inst : ∀ {n} (A : Algebra {a} {ℓ₁})
       → Env A n → F n ⟿ A
inst A θ = fold A (lift θ)

∣inst∣-args : ∀ {n m} (A : Algebra {a} {ℓ₁})
              → Env A n
              → Vec ∥ F n ∥ m
              → Vec ∥ A ∥ m
∣inst∣-args A θ = ∣fold∣-args A (lift θ)

module _ {n}
  {S : Setoid a ℓ₁}
  (T : Setoid b ℓ₂)
  (f : S ↝ T)
  (g : Fin n → Setoid.Carrier T)
  where

  open Setoid S renaming (Carrier to A) using ()
  open Setoid T renaming (Carrier to B)

  ∣sub∣ : BT A n → B
  ∣sub∣ (sta x) = Morphism.∣ f ∣ x
  ∣sub∣ (dyn x) = g x

  ∣sub∣-cong : Congruent (_≑_ {S = S}) _≈_ ∣sub∣
  ∣sub∣-cong (sta p) = Morphism.∣ f ∣-cong p
  ∣sub∣-cong (dyn q) = reflexive (PE.cong g q)

  sub : Atoms S n ↝ T
  sub = record { ∣_∣      = ∣sub∣
               ; ∣_∣-cong = ∣sub∣-cong
               }
module _ {n}
  {A : Algebra {a} {ℓ₁}}
  (B : Algebra {b} {ℓ₂})
  (f : ∥ A ∥/≈ ↝ ∥ B ∥/≈)
  (g : Fin n → ∥ B ∥)
  where

  subst : Free (Atoms ∥ A ∥/≈ n) ⟿ B
  subst = fold B (sub ∥ B ∥/≈ f g)

  ∣subst∣-args : ∀ {m} → Vec (Term (BT ∥ A ∥ n)) m
                 → Vec ∥ B ∥ m
  ∣subst∣-args = ∣fold∣-args B (sub ∥ B ∥/≈ f g)
