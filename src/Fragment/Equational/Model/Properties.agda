{-# OPTIONS --without-K --exact-split --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Model.Properties (Θ : Theory) where

open import Fragment.Equational.Model.Base Θ
open import Fragment.Equational.Model.Synthetic Θ
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Free (Σ Θ)
open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level)
open import Function using (_∘_)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc; fromℕ)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as Reasoning

private
  variable
    a ℓ : Level

module _ {n} (A : Model {a} {ℓ}) (θ : Env ∥ A ∥ₐ n) where

  private

    module S = Setoid ∥ A ∥/≈
    open Reasoning ∥ A ∥/≈

    mutual
      map-∣interp∣-cong : ∀ {m} {xs ys : Vec ∥ J n ∥ m}
                          → Pointwise ≈[ J n ] xs ys
                          → Pointwise ≈[ A ] (map ∣ inst ∥ A ∥ₐ θ ∣ xs)
                                             (map ∣ inst ∥ A ∥ₐ θ ∣ ys)
      map-∣interp∣-cong []       = []
      map-∣interp∣-cong (p ∷ ps) = ∣interp∣-cong p ∷ map-∣interp∣-cong ps

      ∣interp∣-cong : Congruent ≈[ J n ] ≈[ A ] ∣ inst ∥ A ∥ₐ θ ∣
      ∣interp∣-cong refl          = S.refl
      ∣interp∣-cong (sym p)       = S.sym (∣interp∣-cong p)
      ∣interp∣-cong (trans p q)   = S.trans (∣interp∣-cong p) (∣interp∣-cong q)
      ∣interp∣-cong (inherit p)   = ∣ inst ∥ A ∥ₐ θ ∣-cong p
      ∣interp∣-cong (cong f {xs = xs} {ys = ys} ps) = begin
          ∣ inst ∥ A ∥ₐ θ ∣ (term f xs)
        ≈⟨ S.sym (∣ inst ∥ A ∥ₐ θ ∣-hom f xs) ⟩
          A ⟦ f ⟧ (map ∣ inst ∥ A ∥ₐ θ ∣ xs)
        ≈⟨ (A ⟦ f ⟧-cong) (map-∣interp∣-cong ps) ⟩
          A ⟦ f ⟧ (map ∣ inst ∥ A ∥ₐ θ ∣ ys)
        ≈⟨ ∣ inst ∥ A ∥ₐ θ ∣-hom f ys ⟩
          ∣ inst ∥ A ∥ₐ θ ∣ (term f ys)
        ∎
      ∣interp∣-cong (axiom eq θ') = begin
          ∣ inst ∥ A ∥ₐ θ ∣ (∣ inst (F n) θ' ∣ lhs)
        ≈⟨ inst-assoc (F n) θ' (inst ∥ A ∥ₐ θ) {x = lhs} ⟩
          ∣ inst ∥ A ∥ₐ (∣ inst ∥ A ∥ₐ θ ∣ ∘ θ') ∣ lhs
        ≈⟨ ∥ A ∥ₐ-models eq _ ⟩
          ∣ inst ∥ A ∥ₐ (∣ inst ∥ A ∥ₐ θ ∣ ∘ θ') ∣ rhs
        ≈⟨ S.sym (inst-assoc (F n) θ' (inst ∥ A ∥ₐ θ) {x = rhs}) ⟩
          ∣ inst ∥ A ∥ₐ θ ∣ (∣ inst (F n) θ' ∣ rhs)
        ∎
        where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
              rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

    ∣interp∣⃗ : ∥ J n ∥/≈ ↝ ∥ A ∥/≈
    ∣interp∣⃗ = record { ∣_∣      = ∣ inst ∥ A ∥ₐ θ ∣
                       ; ∣_∣-cong = ∣interp∣-cong
                       }

  interp : ∥ J n ∥ₐ ⟿ ∥ A ∥ₐ
  interp = record { ∣_∣⃗    = ∣interp∣⃗
                  ; ∣_∣-hom = ∣ inst ∥ A ∥ₐ θ ∣-hom
                  }

atomise : (n : ℕ) → ∥ J (suc n) ∥
atomise n = atom (dyn (fromℕ n))

up : ∀ {n} → Fin n → Fin (suc n)
up zero    = zero
up (suc n) = suc (up n)

raise : ∀ {n} → ∥ J n ∥ₐ ⟿ ∥ J (suc n) ∥ₐ
raise {n} = interp (J (suc n)) (λ k → atom (dyn (up k)))

step : ∀ {n} → ∥ J n ∥ₐ ⟿ ∥ J (suc n) ∥ₐ
step {n} = interp (J (suc n)) (λ k → atom (dyn (suc k)))

mutual

  map-step-raise : ∀ {n m} → (xs : Vec ∥ J n ∥ m)
                   → Pointwise ≈[ J (suc (suc n)) ]
                               (map ∣ step {suc n} ⊙ raise {n} ∣ xs)
                               (map ∣ raise {suc n} ⊙ step {n} ∣ xs)
  map-step-raise []       = []
  map-step-raise (x ∷ xs) = step-raise {x = x} ∷ map-step-raise xs

  step-raise : ∀ {n} → step {suc n} ⊙ raise {n} ≗ raise {suc n} ⊙ step {n}
  step-raise {n} {atom (dyn k)} = refl
  step-raise {n} {term f xs}    = begin
      ∣ step ⊙ raise ∣ (term f xs)
    ≈⟨ sym (∣ step ⊙ raise ∣-hom f xs) ⟩
      term f (map ∣ step ⊙ raise ∣ xs)
    ≈⟨ cong f (map-step-raise xs) ⟩
      term f (map ∣ raise ⊙ step ∣ xs)
    ≈⟨ ∣ raise ⊙ step ∣-hom f xs ⟩
      ∣ raise ⊙ step ∣ (term f xs)
    ∎
    where open Reasoning ∥ J (suc (suc n)) ∥/≈
