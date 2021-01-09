{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Category (Σ : Signature) where

  open import Relation.Binary using (Setoid; IsEquivalence)
  open import Relation.Binary.PropositionalEquality using (_≡_; cong)
  open import Function
  open import Data.Vec
  open import Data.Vec.Properties using (map-id)

  open import Fragment.Algebra.Algebra
  open import Fragment.Algebra.Homomorphism

  module _ {a ℓ} {S : Setoid a ℓ} (Sᴬ : IsAlgebra S Σ) where

    open Setoid S renaming (Carrier to A)
    open IsAlgebra Sᴬ

    id-hom : ∀ {arity} → (f : ops Σ arity)
             → (xs : Vec A arity)
             → ⟦ f ⟧ xs ≈ ⟦ f ⟧ (map id xs)
    id-hom f xs = ?

    idₕ : Homomorphism Sᴬ Sᴬ
    idₕ = record { h     = id
                 ; h-hom = id-hom
                 }
