{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.TermAlgebra.Syntax (Σ : Signature) where

open import Fragment.Algebra.TermAlgebra.Base Σ

open import Data.Vec using ([]; _∷_)

⟨_⟩₀ : ops Σ 0 → Expr
⟨ f ⟩₀ = term f []

⟨_⟩₁_ : ops Σ 1 → Expr → Expr
⟨ f ⟩₁ t = term f (t ∷ [])

_⟨_⟩₂_ : Expr → ops Σ 2 → Expr → Expr
s ⟨ f ⟩₂ t = term f (s ∷ t ∷ [])
