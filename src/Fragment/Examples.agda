{-# OPTIONS --without-K --safe #-}

module Fragment.Examples where

open import Fragment.Equational.Bundles using (Θ-semigroup; Σ-magma; MagmaOp)
open import Fragment.Equational.Model
open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.Structures using (semigroup→isModel)

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Homomorphism (Σ-magma)
open import Fragment.Algebra.TermAlgebra using (Expr)
open import Fragment.Algebra.FreeAlgebra
open import Fragment.Algebra.Algebra

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-isSemigroup)
open import Data.Vec using ([]; _∷_)
open import Data.Fin using (Fin; zero; suc; #_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Function using (_∘_)

open import Fragment.Macros.Fin

open import Algebra.Structures using (IsSemigroup)

+-isModel : IsModel Θ-semigroup (PE.setoid ℕ)
+-isModel = semigroup→isModel (PE.setoid ℕ) +-isSemigroup

+-model : Model Θ-semigroup
+-model = record { isModel = +-isModel; Carrierₛ = PE.setoid ℕ }

+-algebra : Algebra Σ-magma
+-algebra = algebra (PE.setoid ℕ) (IsModel.isAlgebra +-isModel)

open import Fragment.Extensions.Semigroup +-isModel 2
open PE.≡-Reasoning

module _ {m n : ℕ} where
  lhsStructure : Expr (Σ-magma ⦉ 4 ⦊)
  lhsStructure =
    (⟨ inj₂ (# 0) ⟩₀ ⟨ MagmaOp.• ⟩₂ ⟨ inj₂ (# 1) ⟩₀)
      ⟨ MagmaOp.• ⟩₂
    (⟨ inj₂ (# 2) ⟩₀ ⟨ MagmaOp.• ⟩₂ ⟨ inj₂ (# 3) ⟩₀)
    where open import Fragment.Algebra.TermAlgebra.Syntax (Σ-magma ⦉ 4 ⦊)

  lhs-α : Fin 4 → NormalSemigroup
  lhs-α zero                   = ++-inr-θ (# 0)
  lhs-α (suc zero)             = ++-inl 2
  lhs-α (suc (suc zero))       = ++-inl 3
  lhs-α (suc (suc (suc zero))) = ++-inr-θ (# 1)

  lhs-ω : Fin 4 → ℕ
  lhs-ω zero                   = m
  lhs-ω (suc zero)             = 2
  lhs-ω (suc (suc zero))       = 3
  lhs-ω (suc (suc (suc zero))) = n

  lhs : NormalSemigroup
  lhs = subst ++-algebra lhs-α lhsStructure

  rhsStructure : Expr (Σ-magma ⦉ 3 ⦊)
  rhsStructure =
    (⟨ inj₂ (# 0) ⟩₀ ⟨ MagmaOp.• ⟩₂ ⟨ inj₂ (# 1) ⟩₀) ⟨ MagmaOp.• ⟩₂ ⟨ inj₂ (# 2) ⟩₀
    where open import Fragment.Algebra.TermAlgebra.Syntax (Σ-magma ⦉ 3 ⦊)

  rhs-α : Fin 3 → NormalSemigroup
  rhs-α zero                   = ++-inr-θ (# 0)
  rhs-α (suc zero)             = ++-inl 5
  rhs-α (suc (suc zero))       = ++-inr-θ (# 1)

  rhs-ω : Fin 3 → ℕ
  rhs-ω zero                   = m
  rhs-ω (suc zero)             = 5
  rhs-ω (suc (suc zero))       = n

  rhs : NormalSemigroup
  rhs = subst ++-algebra rhs-α rhsStructure

  θ : Fin 2 → ℕ
  θ zero       = m
  θ (suc zero) = n

  factor-p : ∀ {k : Fin 4} → reduce ++-isFrex θ (lhs-α k) ≡ lhs-ω k
  factor-p = fin-refl 4 ((reduce ++-isFrex θ) ∘ lhs-α) lhs-ω

  p : reduce ++-isFrex θ lhs ≡ (m + 2) + (3 + n)
  p = factor ++-isFrex lhs-ω lhs-α θ factor-p {x = lhsStructure}

  factor-q : ∀ {k : Fin 3} → reduce ++-isFrex θ (rhs-α k) ≡ rhs-ω k
  factor-q = fin-refl 3 ((reduce ++-isFrex θ) ∘ rhs-α) rhs-ω

  q : reduce ++-isFrex θ rhs ≡ (m + 5) + n
  q = factor ++-isFrex rhs-ω rhs-α θ factor-q {x = rhsStructure}

  simple : (m + 2) + (3 + n) ≡ (m + 5) + n
  simple = fundamental ++-isFrex {x' = lhs} {y' = rhs} θ p q PE.refl
