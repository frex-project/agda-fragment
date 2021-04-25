{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.CSemigroup.Monomial where

open import Fragment.Equational.Theory.Bundles

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Free Σ-magma hiding (_~_)
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence)
open import Fragment.Equational.Model Θ-csemigroup

open import Fragment.Setoid.Morphism using (_↝_)

open import Fragment.Extensions.CSemigroup.Nat

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; #_; fromℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

data Monomial : ℕ → Set where
  leaf : ∀ {n} → ℕ⁺ → Monomial (suc n)
  skip : ∀ {n} → Monomial n → Monomial (suc n)
  cons : ∀ {n} → ℕ⁺ → Monomial n → Monomial (suc n)

_⊗_ : ∀ {n} → Monomial n → Monomial n → Monomial n
leaf x    ⊗ leaf y    = leaf (x + y)
leaf x    ⊗ skip y    = cons x y
leaf x    ⊗ cons y ys = cons (x + y) ys
skip x    ⊗ leaf y    = cons y x
skip x    ⊗ skip y    = skip (x ⊗ y)
skip x    ⊗ cons y ys = cons y (x ⊗ ys)
cons x xs ⊗ leaf y    = cons (x + y) xs
cons x xs ⊗ skip y    = cons x (xs ⊗ y)
cons x xs ⊗ cons y ys = cons (x + y) (xs ⊗ ys)

⊗-cong : ∀ {n} {x y z w : Monomial n}
         → x ≡ y → z ≡ w → x ⊗ z ≡ y ⊗ w
⊗-cong = PE.cong₂ _⊗_

⊗-comm : ∀ {n} (x y : Monomial n) → x ⊗ y ≡ y ⊗ x
⊗-comm (leaf x)    (leaf y)    = PE.cong leaf (+-comm x y)
⊗-comm (leaf x)    (skip y)    = PE.refl
⊗-comm (leaf x)    (cons y ys) = PE.cong₂ cons (+-comm x y) PE.refl
⊗-comm (skip x)    (leaf y)    = PE.refl
⊗-comm (skip x)    (skip y)    = PE.cong skip (⊗-comm x y)
⊗-comm (skip x)    (cons y ys) = PE.cong (cons y) (⊗-comm x ys)
⊗-comm (cons x xs) (leaf y)    = PE.cong₂ cons (+-comm x y) PE.refl
⊗-comm (cons x xs) (skip y)    = PE.cong (cons x) (⊗-comm xs y)
⊗-comm (cons x xs) (cons y ys) = PE.cong₂ cons (+-comm x y) (⊗-comm xs ys)

⊗-assoc : ∀ {n} (x y z : Monomial n) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
⊗-assoc (leaf x)    (leaf y)    (leaf z)    = PE.cong leaf (+-assoc x y z)
⊗-assoc (leaf x)    (leaf y)    (skip z)    = PE.refl
⊗-assoc (leaf x)    (leaf y)    (cons z zs) = PE.cong₂ cons (+-assoc x y z) PE.refl
⊗-assoc (leaf x)    (skip y)    (leaf z)    = PE.refl
⊗-assoc (leaf x)    (skip y)    (skip z)    = PE.refl
⊗-assoc (leaf x)    (skip y)    (cons z zs) = PE.refl
⊗-assoc (leaf x)    (cons y ys) (leaf z)    = PE.cong₂ cons (+-assoc x y z) PE.refl
⊗-assoc (leaf x)    (cons y ys) (skip z)    = PE.refl
⊗-assoc (leaf x)    (cons y ys) (cons z zs) = PE.cong₂ cons (+-assoc x y z) PE.refl
⊗-assoc (skip x)    (leaf y)    (leaf z)    = PE.refl
⊗-assoc (skip x)    (leaf y)    (skip z)    = PE.refl
⊗-assoc (skip x)    (leaf y)    (cons z zs) = PE.refl
⊗-assoc (skip x)    (skip y)    (leaf z)    = PE.refl
⊗-assoc (skip x)    (skip y)    (skip z)    = PE.cong skip (⊗-assoc x y z)
⊗-assoc (skip x)    (skip y)    (cons z zs) = PE.cong (cons z) (⊗-assoc x y zs)
⊗-assoc (skip x)    (cons y ys) (leaf z)    = PE.refl
⊗-assoc (skip x)    (cons y ys) (skip z)    = PE.cong (cons y) (⊗-assoc x ys z)
⊗-assoc (skip x)    (cons y ys) (cons z zs) = PE.cong (cons (y + z)) (⊗-assoc x ys zs)
⊗-assoc (cons x xs) (leaf y)    (leaf z)    = PE.cong₂ cons (+-assoc x y z) PE.refl
⊗-assoc (cons x xs) (leaf y)    (skip z)    = PE.refl
⊗-assoc (cons x xs) (leaf y)    (cons z zs) = PE.cong₂ cons (+-assoc x y z) PE.refl
⊗-assoc (cons x xs) (skip y)    (leaf z)    = PE.refl
⊗-assoc (cons x xs) (skip y)    (skip z)    = PE.cong (cons x) (⊗-assoc xs y z)
⊗-assoc (cons x xs) (skip y)    (cons z zs) = PE.cong (cons (x + z)) (⊗-assoc xs y zs)
⊗-assoc (cons x xs) (cons y ys) (leaf z)    = PE.cong₂ cons (+-assoc x y z) PE.refl
⊗-assoc (cons x xs) (cons y ys) (skip z)    = PE.cong (cons (x + y)) (⊗-assoc xs ys z)
⊗-assoc (cons x xs) (cons y ys) (cons z zs) = PE.cong₂ cons (+-assoc x y z) (⊗-assoc xs ys zs)

module _ (n : ℕ) where

  private

    Monomial/≡ : Setoid _ _
    Monomial/≡ = PE.setoid (Monomial n)

    Monomial⟦_⟧ : Interpretation Monomial/≡
    Monomial⟦ • ⟧ (x ∷ y ∷ []) = x ⊗ y

    Monomial⟦_⟧-cong : Congruence Monomial/≡ Monomial⟦_⟧
    Monomial⟦ • ⟧-cong (p ∷ q ∷ []) = PE.cong₂ _⊗_ p q

    Monomial/≡-isAlgebra : IsAlgebra (Monomial/≡)
    Monomial/≡-isAlgebra = record { ⟦_⟧     = Monomial⟦_⟧
                                  ; ⟦⟧-cong = Monomial⟦_⟧-cong
                                  }

    Monomial/≡-algebra : Algebra
    Monomial/≡-algebra =
      record { ∥_∥/≈           = Monomial/≡
             ; ∥_∥/≈-isAlgebra = Monomial/≡-isAlgebra
             }

    Monomial/≡-models : Models Monomial/≡-algebra
    Monomial/≡-models comm θ  = ⊗-comm (θ (# 0)) (θ (# 1))
    Monomial/≡-models assoc θ = ⊗-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

    Monomial/≡-isModel : IsModel Monomial/≡
    Monomial/≡-isModel =
      record { isAlgebra = Monomial/≡-isAlgebra
             ; models    = Monomial/≡-models
             }

  J' : Model
  J' = record { ∥_∥/≈   = Monomial/≡
              ; isModel = Monomial/≡-isModel
              }

private

  module _ {n : ℕ} where

    open Setoid ∥ J n ∥/≈ using (_≈_)

    _·_ : ∥ J n ∥ → ∥ J n ∥ → ∥ J n ∥
    x · y = term • (x ∷ y ∷ [])

    ·-cong : ∀ {x y z w} → x ≈ y → z ≈ w → x · z ≈ y · w
    ·-cong p q = cong • (p ∷ q ∷ [])

    ·-comm : ∀ x y → x · y ≈ y · x
    ·-comm x y = axiom comm (env {A = ∥ J n ∥ₐ} (x ∷ y ∷ []))

    ·-assoc : ∀ x y z → (x · y) · z ≈ x · (y · z)
    ·-assoc x y z = axiom assoc (env {A = ∥ J n ∥ₐ} (x ∷ y ∷ z ∷ []))

  module _ (n : ℕ) where

    open Setoid ∥ J (suc n) ∥/≈ using (_≈_)

    exp : ℕ⁺ → ∥ J (suc n) ∥
    exp one     = atomise n
    exp (suc k) = atomise n · exp k

    exp-hom : ∀ {j k} → exp j · exp k ≈ exp (j + k)
    exp-hom {one}   {k} = refl
    exp-hom {suc j} {k} = begin
        (atomise n · exp j) · exp k
      ≈⟨ ·-assoc (atomise n) (exp j) (exp k) ⟩
        atomise n · (exp j · exp k)
      ≈⟨ ·-cong refl exp-hom ⟩
        atomise n · exp (j + k)
      ∎
      where open Reasoning ∥ J (suc n) ∥/≈

  ∣norm∣ : ∀ {n} → ∥ J' n ∥ → ∥ J n ∥
  ∣norm∣ {suc n} (leaf k)    = exp n k
  ∣norm∣ {suc n} (skip x)    = ∣ raise ∣ (∣norm∣ x)
  ∣norm∣ {suc n} (cons k xs) = exp n k · ∣ raise ∣ (∣norm∣ xs)

  ∣norm∣-cong : ∀ {n} → Congruent _≡_ ≈[ J n ] ∣norm∣
  ∣norm∣-cong {n} p = Setoid.reflexive ∥ J n ∥/≈ (PE.cong ∣norm∣ p)

  ∣norm∣⃗ : ∀ {n} → ∥ J' n ∥/≈ ↝ ∥ J n ∥/≈
  ∣norm∣⃗ {n} = record { ∣_∣      = ∣norm∣ {n}
                       ; ∣_∣-cong = ∣norm∣-cong {n}
                       }

  ∣norm∣-hom : ∀ {n} → Homomorphic ∥ J' n ∥ₐ ∥ J n ∥ₐ ∣norm∣
  ∣norm∣-hom {suc n} • (leaf x    ∷ leaf y    ∷ []) = exp-hom n
  ∣norm∣-hom {suc n} • (leaf x    ∷ skip y    ∷ []) = refl
  ∣norm∣-hom {suc n} • (leaf x    ∷ cons y ys ∷ []) = begin
      exp n x · (exp n y · ∣ raise ∣ (∣norm∣ ys))
    ≈⟨ sym (·-assoc (exp n x) (exp n y) _) ⟩
      (exp n x · exp n y) · ∣ raise ∣ (∣norm∣ ys)
    ≈⟨ ·-cong (exp-hom n) refl ⟩
      exp n (x + y) · ∣ raise ∣ (∣norm∣ ys)
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣norm∣-hom {suc n} • (skip x    ∷ leaf y    ∷ []) = ·-comm _ (exp n y)
  ∣norm∣-hom {suc n} • (skip x    ∷ skip y    ∷ []) = begin
      ∣ raise ∣ (∣norm∣ x) · ∣ raise ∣ (∣norm∣ y)
    ≈⟨ ∣ raise ∣-hom • (∣norm∣ x ∷ ∣norm∣ y ∷ []) ⟩
      ∣ raise ∣ (∣norm∣ x · ∣norm∣ y)
    ≈⟨ ∣ raise ∣-cong (∣norm∣-hom • (x ∷ y ∷ [])) ⟩
      ∣ raise ∣ (∣norm∣ (x ⊗ y))
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣norm∣-hom {suc n} • (skip x    ∷ cons y ys ∷ []) = begin
      ∣ raise ∣ (∣norm∣ x) · (exp n y · ∣ raise ∣ (∣norm∣ ys))
    ≈⟨ sym (·-assoc _ (exp n y) _) ⟩
      (∣ raise ∣ (∣norm∣ x) · exp n y) · ∣ raise ∣ (∣norm∣ ys)
    ≈⟨ ·-cong (·-comm _ (exp n y)) refl ⟩
      (exp n y · ∣ raise ∣ (∣norm∣ x)) · ∣ raise ∣ (∣norm∣ ys)
    ≈⟨ ·-assoc (exp n y) _ _ ⟩
      exp n y · (∣ raise ∣ (∣norm∣ x) · ∣ raise ∣ (∣norm∣ ys))
    ≈⟨ ·-cong refl (∣ raise ∣-hom • (∣norm∣ x ∷ ∣norm∣ ys ∷ [])) ⟩
      exp n y · ∣ raise ∣ (∣norm∣ x · ∣norm∣ ys)
    ≈⟨ ·-cong refl (∣ raise ∣-cong (∣norm∣-hom • (x ∷ ys ∷ []))) ⟩
      exp n y · ∣ raise ∣ (∣norm∣ (x ⊗ ys))
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣norm∣-hom {suc n} • (cons x xs ∷ leaf y    ∷ []) = begin
      (exp n x · ∣ raise ∣ (∣norm∣ xs)) · exp n y
    ≈⟨ ·-assoc (exp n x) _ (exp n y) ⟩
      exp n x · (∣ raise ∣ (∣norm∣ xs) · exp n y)
    ≈⟨ ·-cong refl (·-comm _ (exp n y)) ⟩
      exp n x · (exp n y · ∣ raise ∣ (∣norm∣ xs))
    ≈⟨ sym (·-assoc (exp n x) (exp n y) _) ⟩
      (exp n x · exp n y) · ∣ raise ∣ (∣norm∣ xs)
    ≈⟨ ·-cong (exp-hom n) refl ⟩
      exp n (x + y) · ∣ raise ∣ (∣norm∣ xs)
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣norm∣-hom {suc n} • (cons x xs ∷ skip y    ∷ []) = begin
      (exp n x · ∣ raise ∣ (∣norm∣ xs)) · ∣ raise ∣ (∣norm∣ y)
    ≈⟨ ·-assoc (exp n x) _ _ ⟩
      exp n x · (∣ raise ∣ (∣norm∣ xs) · ∣ raise ∣ (∣norm∣ y))
    ≈⟨ ·-cong refl (∣ raise ∣-hom • (∣norm∣ xs ∷ ∣norm∣ y ∷ [])) ⟩
      exp n x · ∣ raise ∣ (∣norm∣ xs · ∣norm∣ y)
    ≈⟨ ·-cong refl (∣ raise ∣-cong (∣norm∣-hom • (xs ∷ y ∷ []))) ⟩
      exp n x · ∣ raise ∣ (∣norm∣ (xs ⊗ y))
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣norm∣-hom {suc n} • (cons x xs ∷ cons y ys ∷ []) = begin
      (exp n x · ∣ raise ∣ (∣norm∣ xs)) · (exp n y · ∣ raise ∣ (∣norm∣ ys))
    ≈⟨ ·-assoc (exp n x) _ _ ⟩
      exp n x · (∣ raise ∣ (∣norm∣ xs) · (exp n y · ∣ raise ∣ (∣norm∣ ys)))
    ≈⟨ ·-cong refl (sym (·-assoc _ (exp n y) _)) ⟩
      exp n x · ((∣ raise ∣ (∣norm∣ xs) · exp n y) · ∣ raise ∣ (∣norm∣ ys))
    ≈⟨ ·-cong refl (·-cong (·-comm (∣ raise ∣ (∣norm∣ xs)) _) refl) ⟩
      exp n x · ((exp n y · ∣ raise ∣ (∣norm∣ xs)) · ∣ raise ∣ (∣norm∣ ys))
    ≈⟨ ·-cong refl (·-assoc (exp n y) _ _) ⟩
      exp n x · (exp n y · (∣ raise ∣ (∣norm∣ xs) · ∣ raise ∣ (∣norm∣ ys)))
    ≈⟨ sym (·-assoc (exp n x) (exp n y) _) ⟩
      (exp n x · exp n y) · (∣ raise ∣ (∣norm∣ xs) · ∣ raise ∣ (∣norm∣ ys))
    ≈⟨ ·-cong (exp-hom n) (∣ raise ∣-hom • (∣norm∣ xs ∷ ∣norm∣ ys ∷ [])) ⟩
      exp n (x + y) · ∣ raise ∣ (∣norm∣ xs · ∣norm∣ ys)
    ≈⟨ ·-cong refl (∣ raise ∣-cong (∣norm∣-hom • (xs ∷ ys ∷ []))) ⟩
      exp n (x + y) · ∣ raise ∣ (∣norm∣ (xs ⊗ ys))
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
