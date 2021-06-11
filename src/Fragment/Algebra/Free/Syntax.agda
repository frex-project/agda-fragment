{-# OPTIONS --without-K --exact-split --safe #-}

open import Fragment.Algebra.Signature
open import Relation.Binary using (Setoid)

module Fragment.Algebra.Free.Syntax {a ℓ}
  (Σ : Signature)
  (A : Setoid a ℓ)
  where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Free.Base Σ

open import Data.Fin using (Fin)
open import Data.Vec using ([]; _∷_)

module _ {n} where

  ⟨_⟩ : Fin n → ∥ Free (Atoms A n) ∥
  ⟨ n ⟩ = atom (dyn n)

  ⟨_⟩ₛ : Setoid.Carrier A → ∥ Free (Atoms A n) ∥
  ⟨ x ⟩ₛ = atom (sta x)

  ⟨_⟩₀ : ops Σ 0 → ∥ Free (Atoms A n) ∥
  ⟨ f ⟩₀ = term f []

  ⟨_⟩₁_ : ops Σ 1 → ∥ Free (Atoms A n) ∥ → ∥ Free (Atoms A n) ∥
  ⟨ f ⟩₁ t = term f (t ∷ [])

  _⟨_⟩₂_ : ∥ Free (Atoms A n) ∥
           → ops Σ 2
           → ∥ Free (Atoms A n) ∥
           → ∥ Free (Atoms A n) ∥
  s ⟨ f ⟩₂ t = term f (s ∷ t ∷ [])
