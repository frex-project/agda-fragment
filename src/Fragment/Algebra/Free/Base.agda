{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Base (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ

open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ (A : Set a) where

  data Term : Set a where
    atom : A → Term
    term : ∀ {arity} → (f : ops Σ arity) → Vec Term arity → Term

  data BT (n : ℕ) : Set a where
    sta : A → BT n
    dyn : Fin n → BT n

module _ (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  data _∼_ : Term A → Term A → Set (a ⊔ ℓ) where
    atom : ∀ {x y} → x ≈ y → atom x ∼ atom y
    term : ∀ {arity xs ys} {f : ops Σ arity}
           → Pointwise _∼_ xs ys
           → term f xs ∼ term f ys

  mutual
    ∼-refl-args : ∀ {n} {xs : Vec _ n} → Pointwise _∼_ xs xs
    ∼-refl-args {xs = []}     = []
    ∼-refl-args {xs = x ∷ xs} = ∼-refl ∷ ∼-refl-args

    ∼-refl : ∀ {x} → x ∼ x
    ∼-refl {atom _}   = atom refl
    ∼-refl {term _ _} = term ∼-refl-args

  mutual
    ∼-sym-args : ∀ {n} {xs ys : Vec _ n}
                 → Pointwise _∼_ xs ys
                 → Pointwise _∼_ ys xs
    ∼-sym-args [] = []
    ∼-sym-args (x≈y ∷ xs≈ys) =
      ∼-sym x≈y ∷ ∼-sym-args xs≈ys

    ∼-sym : ∀ {x y} → x ∼ y → y ∼ x
    ∼-sym (atom x≈y)   = atom (sym x≈y)
    ∼-sym (term xs≈ys) = term (∼-sym-args xs≈ys)

  mutual
    ∼-trans-args : ∀ {n} {xs ys zs : Vec _ n}
                   → Pointwise _∼_ xs ys
                   → Pointwise _∼_ ys zs
                   → Pointwise _∼_ xs zs
    ∼-trans-args [] [] = []
    ∼-trans-args (x≈y ∷ xs≈ys) (y≈z ∷ ys≈zs) =
      ∼-trans x≈y y≈z ∷ ∼-trans-args xs≈ys ys≈zs

    ∼-trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z
    ∼-trans (atom x≈y) (atom y≈z)     =
      atom (trans x≈y y≈z)
    ∼-trans (term xs≈ys) (term ys≈zs) =
      term (∼-trans-args xs≈ys ys≈zs)

  ∼-isEquivalence : IsEquivalence _∼_
  ∼-isEquivalence = record { refl  = ∼-refl
                           ; sym   = ∼-sym
                           ; trans = ∼-trans
                           }

  Herbrand : Setoid _ _
  Herbrand = record { Carrier       = Term A
                    ; _≈_           = _∼_
                    ; isEquivalence = ∼-isEquivalence
                    }

  term-cong : Congruence Herbrand term
  term-cong f p = term p

  Free-isAlgebra : IsAlgebra Herbrand
  Free-isAlgebra = record { ⟦_⟧     = term
                          ; ⟦⟧-cong = term-cong
                          }

  Free : Algebra
  Free = record { ∥_∥/≈           = Herbrand
                ; ∥_∥/≈-isAlgebra = Free-isAlgebra
                }

F : ℕ → Algebra
F = Free ∘ PE.setoid ∘ Fin

module _ {S : Setoid a ℓ} {n : ℕ} where

  open Setoid S renaming (Carrier to A)

  data _≑_ : BT A n → BT A n → Set (a ⊔ ℓ) where
    sta : ∀ {x y} → x ≈ y → sta x ≑ sta y
    dyn : ∀ {x y} → x ≡ y → dyn x ≑ dyn y

  ≑-refl : ∀ {x} → x ≑ x
  ≑-refl {sta _} = sta refl
  ≑-refl {dyn _} = dyn PE.refl

  ≑-sym : ∀ {x y} → x ≑ y → y ≑ x
  ≑-sym (sta x≈y) = sta (sym x≈y)
  ≑-sym (dyn x≡y) = dyn (PE.sym x≡y)

  ≑-trans : ∀ {x y z} → x ≑ y → y ≑ z → x ≑ z
  ≑-trans (sta x≈y) (sta y≈z) = sta (trans x≈y y≈z)
  ≑-trans (dyn x≡y) (dyn y≡z) = dyn (PE.trans x≡y y≡z)

  ≑-isEquivalence : IsEquivalence _≑_
  ≑-isEquivalence = record { refl  = ≑-refl
                           ; sym   = ≑-sym
                           ; trans = ≑-trans
                           }

Atoms : Setoid a ℓ → ℕ → Setoid a (a ⊔ ℓ)
Atoms S n = record { Carrier       = BT (Setoid.Carrier S) n
                   ; _≈_           = _≑_ {S = S}
                   ; isEquivalence = ≑-isEquivalence
                   }
