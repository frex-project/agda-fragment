{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Equational.Theory.Laws (Σ : Signature) where

open import Fragment.Equational.Theory.Base using (Eq)

open import Data.Fin using (#_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)

module _ where

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ 1 ⦊)

  private

    a : ops (Σ ⦉ 1 ⦊) 0
    a = inj₂ (# 0)

  dne : ops Σ 1 → Eq Σ 1
  dne ~ = ⟨ ~ ⟩₁ ⟨ ~ ⟩₁ ⟨ a ⟩₀ , ⟨ a ⟩₀

module _ (e : ops Σ 0) where

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ 1 ⦊)

  private

    u : ops (Σ ⦉ 1 ⦊) 0
    u = (inj₁ e)

    a : ops (Σ ⦉ 1 ⦊) 0
    a = inj₂ (# 0)

  idₗ : ops Σ 2 → Eq Σ 1
  idₗ • = ⟨ u ⟩₀ ⟨ • ⟩₂ ⟨ a ⟩₀ , ⟨ a ⟩₀

  idᵣ : ops Σ 2 → Eq Σ 1
  idᵣ • = ⟨ a ⟩₀ ⟨ • ⟩₂ ⟨ u ⟩₀ , ⟨ a ⟩₀

  anₗ : ops Σ 2 → Eq Σ 1
  anₗ • = ⟨ u ⟩₀ ⟨ • ⟩₂ ⟨ a ⟩₀ , ⟨ u ⟩₀

  anᵣ : ops Σ 2 → Eq Σ 1
  anᵣ • = ⟨ a ⟩₀ ⟨ • ⟩₂ ⟨ u ⟩₀ , ⟨ u ⟩₀

  invₗ : ops Σ 1 → ops Σ 2 → Eq Σ 1
  invₗ ~ • = (⟨ ~ ⟩₁ ⟨ a ⟩₀) ⟨ • ⟩₂ ⟨ a ⟩₀ , ⟨ u ⟩₀

  invᵣ : ops Σ 1 → ops Σ 2 → Eq Σ 1
  invᵣ ~ • = ⟨ a ⟩₀ ⟨ • ⟩₂ (⟨ ~ ⟩₁ ⟨ a ⟩₀) , ⟨ u ⟩₀

module _ where

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ 2 ⦊)

  private

    a : ops (Σ ⦉ 2 ⦊) 0
    a = inj₂ (# 0)

    b : ops (Σ ⦉ 2 ⦊) 0
    b = inj₂ (# 1)

  comm : ops Σ 2 → Eq Σ 2
  comm • = ⟨ a ⟩₀ ⟨ • ⟩₂ ⟨ b ⟩₀ , ⟨ b ⟩₀ ⟨ • ⟩₂ ⟨ a ⟩₀

module _ where

  open import Fragment.Algebra.TermAlgebra (Σ ⦉ 3 ⦊)

  private

    a : ops (Σ ⦉ 3 ⦊) 0
    a = inj₂ (# 0)

    b : ops (Σ ⦉ 3 ⦊) 0
    b = inj₂ (# 1)

    c : ops (Σ ⦉ 3 ⦊) 0
    c = inj₂ (# 2)

  assoc : ops Σ 2 → Eq Σ 3
  assoc • =
      (⟨ a ⟩₀ ⟨ • ⟩₂ ⟨ b ⟩₀) ⟨ • ⟩₂ ⟨ c ⟩₀
    ,
      ⟨ a ⟩₀ ⟨ • ⟩₂ (⟨ b ⟩₀ ⟨ • ⟩₂ ⟨ c ⟩₀)
