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

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Fin using (Fin; #_; zero; suc; toℕ; fromℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

open import Relation.Nullary using (yes ; no)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

data Monomial : ℕ → Set where
  leaf : ∀ {n} → ℕ⁺ → Monomial (suc n)
  skip : ∀ {n} → Monomial n → Monomial (suc n)
  cons : ∀ {n} → ℕ⁺ → Monomial n → Monomial (suc n)

lift : ∀ {n} → Monomial n → Monomial (suc n)
lift (leaf x)    = leaf x
lift (skip x)    = skip (lift x)
lift (cons x xs) = cons x (lift xs)

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

  ∣syn∣ : ∀ {n} → ∥ J' n ∥ → ∥ J n ∥
  ∣syn∣ {suc n} (leaf k)    = exp n k
  ∣syn∣ {suc n} (skip x)    = ∣ raise ∣ (∣syn∣ x)
  ∣syn∣ {suc n} (cons k xs) = exp n k · ∣ raise ∣ (∣syn∣ xs)

  ∣syn∣-cong : ∀ {n} → Congruent _≡_ ≈[ J n ] ∣syn∣
  ∣syn∣-cong {n} p = Setoid.reflexive ∥ J n ∥/≈ (PE.cong ∣syn∣ p)

  ∣syn∣⃗ : ∀ {n} → ∥ J' n ∥/≈ ↝ ∥ J n ∥/≈
  ∣syn∣⃗ {n} = record { ∣_∣      = ∣syn∣ {n}
                      ; ∣_∣-cong = ∣syn∣-cong {n}
                      }

  ∣syn∣-hom : ∀ {n} → Homomorphic ∥ J' n ∥ₐ ∥ J n ∥ₐ ∣syn∣
  ∣syn∣-hom {suc n} • (leaf x    ∷ leaf y    ∷ []) = exp-hom n
  ∣syn∣-hom {suc n} • (leaf x    ∷ skip y    ∷ []) = refl
  ∣syn∣-hom {suc n} • (leaf x    ∷ cons y ys ∷ []) = begin
      exp n x · (exp n y · ∣ raise ∣ (∣syn∣ ys))
    ≈⟨ sym (·-assoc (exp n x) (exp n y) _) ⟩
      (exp n x · exp n y) · ∣ raise ∣ (∣syn∣ ys)
    ≈⟨ ·-cong (exp-hom n) refl ⟩
      exp n (x + y) · ∣ raise ∣ (∣syn∣ ys)
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣syn∣-hom {suc n} • (skip x    ∷ leaf y    ∷ []) = ·-comm _ (exp n y)
  ∣syn∣-hom {suc n} • (skip x    ∷ skip y    ∷ []) = begin
      ∣ raise ∣ (∣syn∣ x) · ∣ raise ∣ (∣syn∣ y)
    ≈⟨ ∣ raise ∣-hom • (∣syn∣ x ∷ ∣syn∣ y ∷ []) ⟩
      ∣ raise ∣ (∣syn∣ x · ∣syn∣ y)
    ≈⟨ ∣ raise ∣-cong (∣syn∣-hom • (x ∷ y ∷ [])) ⟩
      ∣ raise ∣ (∣syn∣ (x ⊗ y))
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣syn∣-hom {suc n} • (skip x    ∷ cons y ys ∷ []) = begin
      ∣ raise ∣ (∣syn∣ x) · (exp n y · ∣ raise ∣ (∣syn∣ ys))
    ≈⟨ sym (·-assoc _ (exp n y) _) ⟩
      (∣ raise ∣ (∣syn∣ x) · exp n y) · ∣ raise ∣ (∣syn∣ ys)
    ≈⟨ ·-cong (·-comm _ (exp n y)) refl ⟩
      (exp n y · ∣ raise ∣ (∣syn∣ x)) · ∣ raise ∣ (∣syn∣ ys)
    ≈⟨ ·-assoc (exp n y) _ _ ⟩
      exp n y · (∣ raise ∣ (∣syn∣ x) · ∣ raise ∣ (∣syn∣ ys))
    ≈⟨ ·-cong refl (∣ raise ∣-hom • (∣syn∣ x ∷ ∣syn∣ ys ∷ [])) ⟩
      exp n y · ∣ raise ∣ (∣syn∣ x · ∣syn∣ ys)
    ≈⟨ ·-cong refl (∣ raise ∣-cong (∣syn∣-hom • (x ∷ ys ∷ []))) ⟩
      exp n y · ∣ raise ∣ (∣syn∣ (x ⊗ ys))
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣syn∣-hom {suc n} • (cons x xs ∷ leaf y    ∷ []) = begin
      (exp n x · ∣ raise ∣ (∣syn∣ xs)) · exp n y
    ≈⟨ ·-assoc (exp n x) _ (exp n y) ⟩
      exp n x · (∣ raise ∣ (∣syn∣ xs) · exp n y)
    ≈⟨ ·-cong refl (·-comm _ (exp n y)) ⟩
      exp n x · (exp n y · ∣ raise ∣ (∣syn∣ xs))
    ≈⟨ sym (·-assoc (exp n x) (exp n y) _) ⟩
      (exp n x · exp n y) · ∣ raise ∣ (∣syn∣ xs)
    ≈⟨ ·-cong (exp-hom n) refl ⟩
      exp n (x + y) · ∣ raise ∣ (∣syn∣ xs)
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣syn∣-hom {suc n} • (cons x xs ∷ skip y    ∷ []) = begin
      (exp n x · ∣ raise ∣ (∣syn∣ xs)) · ∣ raise ∣ (∣syn∣ y)
    ≈⟨ ·-assoc (exp n x) _ _ ⟩
      exp n x · (∣ raise ∣ (∣syn∣ xs) · ∣ raise ∣ (∣syn∣ y))
    ≈⟨ ·-cong refl (∣ raise ∣-hom • (∣syn∣ xs ∷ ∣syn∣ y ∷ [])) ⟩
      exp n x · ∣ raise ∣ (∣syn∣ xs · ∣syn∣ y)
    ≈⟨ ·-cong refl (∣ raise ∣-cong (∣syn∣-hom • (xs ∷ y ∷ []))) ⟩
      exp n x · ∣ raise ∣ (∣syn∣ (xs ⊗ y))
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈
  ∣syn∣-hom {suc n} • (cons x xs ∷ cons y ys ∷ []) = begin
      (exp n x · ∣ raise ∣ (∣syn∣ xs)) · (exp n y · ∣ raise ∣ (∣syn∣ ys))
    ≈⟨ ·-assoc (exp n x) _ _ ⟩
      exp n x · (∣ raise ∣ (∣syn∣ xs) · (exp n y · ∣ raise ∣ (∣syn∣ ys)))
    ≈⟨ ·-cong refl (sym (·-assoc _ (exp n y) _)) ⟩
      exp n x · ((∣ raise ∣ (∣syn∣ xs) · exp n y) · ∣ raise ∣ (∣syn∣ ys))
    ≈⟨ ·-cong refl (·-cong (·-comm (∣ raise ∣ (∣syn∣ xs)) _) refl) ⟩
      exp n x · ((exp n y · ∣ raise ∣ (∣syn∣ xs)) · ∣ raise ∣ (∣syn∣ ys))
    ≈⟨ ·-cong refl (·-assoc (exp n y) _ _) ⟩
      exp n x · (exp n y · (∣ raise ∣ (∣syn∣ xs) · ∣ raise ∣ (∣syn∣ ys)))
    ≈⟨ sym (·-assoc (exp n x) (exp n y) _) ⟩
      (exp n x · exp n y) · (∣ raise ∣ (∣syn∣ xs) · ∣ raise ∣ (∣syn∣ ys))
    ≈⟨ ·-cong (exp-hom n) (∣ raise ∣-hom • (∣syn∣ xs ∷ ∣syn∣ ys ∷ [])) ⟩
      exp n (x + y) · ∣ raise ∣ (∣syn∣ xs · ∣syn∣ ys)
    ≈⟨ ·-cong refl (∣ raise ∣-cong (∣syn∣-hom • (xs ∷ ys ∷ []))) ⟩
      exp n (x + y) · ∣ raise ∣ (∣syn∣ (xs ⊗ ys))
    ∎
    where open Reasoning ∥ J (suc n) ∥/≈

syn : ∀ {n} → ∥ J' n ∥ₐ ⟿ ∥ J n ∥ₐ
syn = record { ∣_∣⃗    = ∣syn∣⃗
             ; ∣_∣-hom = ∣syn∣-hom
             }

private

  tab : ∀ {n} → Fin n → ∥ J' n ∥
  tab {suc zero}    zero    = leaf one
  tab {suc (suc n)} zero    = skip (tab {suc n} zero)
  tab {suc (suc n)} (suc k) = lift (tab {suc n} k)

norm : ∀ {n} → ∥ J n ∥ₐ ⟿ ∥ J' n ∥ₐ
norm {n} = interp (J' n) tab

private

  step-exp : ∀ {n} → (k : ℕ⁺)
             → ≈[ J (suc (suc n)) ] (exp (suc n) k)
                                    (∣ step ∣ (exp n k))
  step-exp one     = refl
  step-exp (suc k) = ·-cong refl (step-exp k)

  step-lift : ∀ {n} → (x : ∥ J' n ∥)
              → ≈[ J (suc n) ] (∣ syn ∣ (lift x))
                               (∣ step ∣ (∣ syn ∣ x))
  step-lift {suc n} (leaf x)    = step-exp x
  step-lift {suc n} (skip x)    = begin
      ∣ raise ∣ (∣ syn ∣ (lift x))
    ≈⟨ ∣ raise ∣-cong (step-lift x) ⟩
      ∣ raise ∣ (∣ step ∣ (∣ syn ∣ x))
    ≈⟨ sym (step-raise {x = ∣ syn ∣ x}) ⟩
      ∣ step ∣ (∣ raise ∣ (∣ syn ∣ x))
    ∎
    where open Reasoning ∥ J (suc (suc n)) ∥/≈
  step-lift {suc n} (cons x xs) = begin
      exp (suc n) x · ∣ raise ∣ (∣ syn ∣ (lift xs))
    ≈⟨ ·-cong refl (∣ raise ∣-cong (step-lift xs)) ⟩
      exp (suc n) x · ∣ raise ∣ (∣ step ∣ (∣ syn ∣ xs))
    ≈⟨ ·-cong (step-exp x) (sym (step-raise {x = ∣ syn ∣ xs})) ⟩
      ∣ step ∣ (exp n x) · ∣ step ∣ (∣ raise ∣ (∣ syn ∣ xs))
    ≈⟨ ∣ step ∣-hom • (exp n x ∷ (∣ raise ∣ (∣ syn ∣ xs)) ∷ []) ⟩
      ∣ step ∣ (exp n x · ∣ raise ∣ (∣ syn ∣ xs))
    ∎
    where open Reasoning ∥ J (suc (suc n)) ∥/≈

  syn-tab : ∀ {n} → (k : Fin n)
            → ≈[ J n ] (∣ syn ∣ (tab k)) (atom (dyn k))
  syn-tab {suc zero}    zero    = refl
  syn-tab {suc (suc n)} zero    = ∣ raise ∣-cong (syn-tab zero)
  syn-tab {suc (suc n)} (suc k) = begin
      ∣ syn ∣ (lift (tab {suc n} k))
    ≈⟨ step-lift (tab {suc n} k) ⟩
      ∣ step ∣ (∣ syn ∣ (tab {suc n} k))
    ≈⟨ ∣ step ∣-cong (syn-tab k) ⟩
      ∣ step ∣ (atom (dyn k))
    ∎
    where open Reasoning ∥ J (suc (suc n)) ∥/≈

syn⊙norm≗id : ∀ {n} → syn {n} ⊙ norm {n} ≗ id
syn⊙norm≗id {n} {atom (dyn k)}        = syn-tab k
syn⊙norm≗id {n} {term • (x ∷ y ∷ [])} = begin
    ∣ syn ∣ (∣ norm ∣ x ⊗ ∣ norm ∣ y)
  ≈⟨ sym (∣ syn ∣-hom • (∣ norm ∣ x ∷ ∣ norm ∣ y ∷ [])) ⟩
    ∣ syn ∣ (∣ norm ∣ x) · ∣ syn ∣ (∣ norm ∣ y)
  ≈⟨ ·-cong syn⊙norm≗id syn⊙norm≗id ⟩
    x · y
  ∎
  where open Reasoning ∥ J n ∥/≈

private

  tab-diag : ∀ n → tab {suc n} (fromℕ n) ≡ leaf one
  tab-diag zero    = PE.refl
  tab-diag (suc n) = PE.cong lift (tab-diag n)

  norm-exp : ∀ {n} (k : ℕ⁺) → ∣ norm ∣ (exp n k) ≡ leaf k
  norm-exp {n} one     = tab-diag n
  norm-exp {n} (suc k) = begin
      ∣ norm ∣ (atomise n · exp n k)
    ≈⟨ PE.sym (∣ norm ∣-hom • (atomise n ∷ exp n k ∷ [])) ⟩
      ∣ norm ∣ (atomise n) ⊗ ∣ norm ∣ (exp n k)
    ≈⟨ ⊗-cong (tab-diag n) (norm-exp k) ⟩
      leaf one ⊗ leaf k
    ∎
    where open Reasoning ∥ J' (suc n) ∥/≈

  tab-skip : ∀ {n} → (k : Fin n) → tab {suc n} (up k) ≡ skip (tab {n} k)
  tab-skip {suc zero}    zero    = PE.refl
  tab-skip {suc (suc n)} zero    = PE.refl
  tab-skip {suc (suc n)} (suc k) = PE.cong lift (tab-skip k)

  norm-raise : ∀ {n x} → ∣ norm {suc n} ∣ (∣ raise ∣ x) ≡ skip (∣ norm {n} ∣ x)
  norm-raise {n} {atom (dyn k)}        = tab-skip k
  norm-raise {n} {term • (x ∷ y ∷ [])} = begin
      ∣ norm ∣ (∣ raise ∣ (x · y))
    ≡⟨ ∣ norm ∣-cong (sym (∣ raise ∣-hom • (x ∷ y ∷ []))) ⟩
      ∣ norm ∣ (∣ raise ∣ x · ∣ raise ∣ y)
    ≡⟨ PE.sym (∣ norm ∣-hom • (∣ raise ∣ x ∷ ∣ raise ∣ y ∷ [])) ⟩
      ∣ norm ∣ (∣ raise ∣ x) ⊗ ∣ norm ∣ (∣ raise ∣ y)
    ≡⟨ ⊗-cong (norm-raise {x = x}) (norm-raise {x = y}) ⟩
      skip (∣ norm ∣ x ⊗ ∣ norm ∣ y)
    ≡⟨ PE.cong skip (∣ norm ∣-hom • (x ∷ y ∷ [])) ⟩
      skip (∣ norm ∣ (x · y))
    ∎
    where open PE.≡-Reasoning

norm⊙syn≗id : ∀ {n} → norm {n} ⊙ syn {n} ≗ id
norm⊙syn≗id {suc n} {leaf x} = norm-exp x
norm⊙syn≗id {suc n} {skip x} = begin
    ∣ norm ∣ (∣ raise ∣ (∣ syn ∣ x))
  ≈⟨ norm-raise {x = ∣ syn ∣ x} ⟩
    skip (∣ norm ∣ (∣ syn ∣ x))
  ≈⟨ PE.cong skip norm⊙syn≗id ⟩
    skip x
  ∎
  where open Reasoning ∥ J' (suc n) ∥/≈
norm⊙syn≗id {suc n} {cons x xs} = begin
    ∣ norm ∣ (exp n x · ∣ raise ∣ (∣ syn ∣ xs))
  ≈⟨ PE.sym (∣ norm ∣-hom • (exp n x ∷ ∣ raise ∣ (∣ syn ∣ xs) ∷ [])) ⟩
    ∣ norm ∣ (exp n x) ⊗ ∣ norm ∣ (∣ raise ∣ (∣ syn ∣ xs))
  ≈⟨ ⊗-cong (norm-exp x) (norm-raise {x = ∣ syn ∣ xs}) ⟩
    leaf x ⊗ skip (∣ norm ∣ (∣ syn ∣ xs))
  ≈⟨ ⊗-cong (PE.refl {x = leaf x}) (PE.cong skip (norm⊙syn≗id {x = xs})) ⟩
    leaf x ⊗ skip xs
  ∎
  where open Reasoning ∥ J' (suc n) ∥/≈

iso : ∀ {n} → ∥ J n ∥ₐ ≃ ∥ J' n ∥ₐ
iso = record { _⃗   = norm
             ; _⃖   = syn
             ; invˡ = norm⊙syn≗id
             ; invʳ = syn⊙norm≗id
             }
