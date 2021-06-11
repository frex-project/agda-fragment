{-# OPTIONS --without-K --exact-split --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Evaluation (Σ : Signature) where

open import Fragment.Algebra.Free.Monad Σ
open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Free.Base Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Setoid.Morphism as Morphism

open import Level using (Level)

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid)
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a b ℓ₁ ℓ₂ : Level

module _ (A : Algebra {a} {ℓ₁}) where

  private

    open Setoid ∥ A ∥/≈
    open import Relation.Binary.Reasoning.Setoid ∥ A ∥/≈

    mutual
      map-∣eval∣ : ∀ {n} → Vec (Term ∥ A ∥) n → Vec ∥ A ∥ n
      map-∣eval∣ []       = []
      map-∣eval∣ (x ∷ xs) = ∣eval∣ x ∷ map-∣eval∣ xs

      ∣eval∣ : Term ∥ A ∥ → ∥ A ∥
      ∣eval∣ (atom x)    = x
      ∣eval∣ (term f xs) = A ⟦ f ⟧ (map-∣eval∣ xs)

    mutual
      map-∣eval∣-cong : ∀ {n} {xs ys : Vec (Term ∥ A ∥) n}
                         → Pointwise (_~_ ∥ A ∥/≈) xs ys
                         → Pointwise ≈[ A ] (map-∣eval∣ xs)
                                          (map-∣eval∣ ys)
      map-∣eval∣-cong []       = []
      map-∣eval∣-cong (p ∷ ps) = ∣eval∣-cong p ∷ map-∣eval∣-cong ps

      ∣eval∣-cong : Congruent (_~_ ∥ A ∥/≈) ≈[ A ] ∣eval∣
      ∣eval∣-cong (atom p)                 = p
      ∣eval∣-cong {x = term op _} (term p) =
        (A ⟦ op ⟧-cong) (map-∣eval∣-cong p)

    ∣eval∣⃗ : Herbrand ∥ A ∥/≈ ↝ ∥ A ∥/≈
    ∣eval∣⃗ = record { ∣_∣      = ∣eval∣
                     ; ∣_∣-cong = ∣eval∣-cong
                     }

    ∣eval∣-args≡map : ∀ {n} {xs : Vec (Term ∥ A ∥) n}
                      → Pointwise _≈_ (map-∣eval∣ xs) (map ∣eval∣ xs)
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

env : ∀ {A : Algebra {a} {ℓ₁}} {n} → (Γ : Vec ∥ A ∥ n) → Env A n
env {A = _} {suc n} (x ∷ _)  zero    = x
env {A = A} {suc n} (_ ∷ xs) (suc i) = env {A = A} xs i

module _ {n}
  {S : Setoid a ℓ₁}
  (T : Setoid b ℓ₂)
  (f : S ↝ T)
  (g : Fin n → Setoid.Carrier T)
  where

  private

    open Setoid S renaming (Carrier to A) using ()
    open Setoid T renaming (Carrier to B)

    ∣sub∣ : BT A n → B
    ∣sub∣ (sta x) = Morphism.∣ f ∣ x
    ∣sub∣ (dyn x) = g x

    ∣sub∣-cong : Congruent (_≍_ S n) _≈_ ∣sub∣
    ∣sub∣-cong (sta p) = Morphism.∣ f ∣-cong p
    ∣sub∣-cong (dyn q) = reflexive (PE.cong g q)

  sub : Atoms S n ↝ T
  sub = record { ∣_∣      = ∣sub∣
               ; ∣_∣-cong = ∣sub∣-cong
               }

module _ {n}
  {A : Setoid a ℓ₁}
  (B : Algebra {b} {ℓ₂})
  (f : A ↝ ∥ B ∥/≈)
  (g : Fin n → ∥ B ∥)
  where

  subst : Free (Atoms A n) ⟿ B
  subst = fold B (sub ∥ B ∥/≈ f g)

ignore : ∀ (A : Setoid a ℓ₁) → PE.setoid ⊥ ↝ A
ignore _ = record { ∣_∣      = λ ()
                  ; ∣_∣-cong = λ {}
                  }

inst : ∀ {n} (A : Algebra {a} {ℓ₁})
       → Env A n → F n ⟿ A
inst {n = n} A θ = subst A (ignore ∥ A ∥/≈) θ
