{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Base (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Free.Atoms public

open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Data.Empty using (⊥)
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

module _ (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  data _~_ : Term A → Term A → Set (a ⊔ ℓ) where
      atom : ∀ {x y} → x ≈ y → atom x ~ atom y
      term : ∀ {arity xs ys} {f : ops Σ arity}
             → Pointwise _~_ xs ys
             → term f xs ~ term f ys

  private

    mutual
      map-~-refl : ∀ {n} {xs : Vec _ n} → Pointwise _~_ xs xs
      map-~-refl {xs = []}     = []
      map-~-refl {xs = x ∷ xs} = ~-refl ∷ map-~-refl

      ~-refl : ∀ {x} → x ~ x
      ~-refl {atom _}   = atom refl
      ~-refl {term _ _} = term map-~-refl

    mutual
      map-~-sym : ∀ {n} {xs ys : Vec _ n}
                   → Pointwise _~_ xs ys
                   → Pointwise _~_ ys xs
      map-~-sym [] = []
      map-~-sym (x≈y ∷ xs≈ys) =
        ~-sym x≈y ∷ map-~-sym xs≈ys

      ~-sym : ∀ {x y} → x ~ y → y ~ x
      ~-sym (atom x≈y)   = atom (sym x≈y)
      ~-sym (term xs≈ys) = term (map-~-sym xs≈ys)

    mutual
      map-~-trans : ∀ {n} {xs ys zs : Vec _ n}
                    → Pointwise _~_ xs ys
                    → Pointwise _~_ ys zs
                    → Pointwise _~_ xs zs
      map-~-trans [] [] = []
      map-~-trans (x≈y ∷ xs≈ys) (y≈z ∷ ys≈zs) =
        ~-trans x≈y y≈z ∷ map-~-trans xs≈ys ys≈zs

      ~-trans : ∀ {x y z} → x ~ y → y ~ z → x ~ z
      ~-trans (atom x≈y) (atom y≈z)     =
        atom (trans x≈y y≈z)
      ~-trans (term xs≈ys) (term ys≈zs) =
        term (map-~-trans xs≈ys ys≈zs)

    ~-isEquivalence : IsEquivalence _~_
    ~-isEquivalence = record { refl  = ~-refl
                             ; sym   = ~-sym
                             ; trans = ~-trans
                             }

  Herbrand : Setoid _ _
  Herbrand = record { Carrier       = Term A
                    ; _≈_           = _~_
                    ; isEquivalence = ~-isEquivalence
                    }

  Free : Algebra
  Free = record { ∥_∥/≈           = Herbrand
                ; ∥_∥/≈-isAlgebra = Free-isAlgebra
                }
    where term-cong : Congruence Herbrand term
          term-cong f p = term p

          Free-isAlgebra : IsAlgebra Herbrand
          Free-isAlgebra = record { ⟦_⟧     = term
                                  ; ⟦⟧-cong = term-cong
                                  }

F : ℕ → Algebra
F = Free ∘ Atoms (PE.setoid ⊥)
