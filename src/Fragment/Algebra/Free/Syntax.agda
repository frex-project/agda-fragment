{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Syntax (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Free.Base Σ

open import Data.Fin using (Fin)
open import Data.Vec using ([]; _∷_)

⟨_⟩ : ∀ {n} → Fin n → ∥ F n ∥
⟨ n ⟩ = atom (dyn n)

⟨_⟩₀ : ∀ {n} → ops Σ 0 → ∥ F n ∥
⟨ f ⟩₀ = term f []

⟨_⟩₁_ : ∀ {n} → ops Σ 1 → ∥ F n ∥ → ∥ F n ∥
⟨ f ⟩₁ t = term f (t ∷ [])

_⟨_⟩₂_ : ∀ {n} → ∥ F n ∥ → ops Σ 2 → ∥ F n ∥ → ∥ F n ∥
s ⟨ f ⟩₂ t = term f (s ∷ t ∷ [])
