{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Equational (Θ : Theory) where

{-
open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level

module _ (S : Setoid a ℓ) where

  open import Data.Fin using (Fin)
  open import Data.List.Relation.Unary.All using (All)

  open Theory Θ
  open Setoid S renaming (Carrier to A)

  open import Fragment.Algebra.Algebra Σ

  Model : Set a
  Model = ∀ {arity} → All (eqs Θ arity) (S ⊨_)

  record IsEquational : Set (a ⊔ ℓ) where
    field
      isAlgebra : IsAlgebra S
      model     : Model
-}
