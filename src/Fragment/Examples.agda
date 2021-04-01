{-# OPTIONS --without-K --safe #-}

module Fragment.Examples where

open import Fragment.Equational.Bundles using (Θ-semigroup; Σ-magma; MagmaOp)
open import Fragment.Equational.Model using (Model; IsModel)
open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.Structures using (semigroup→isModel)

open import Fragment.Algebra.Signature
open import Fragment.Algebra.TermAlgebra using (Expr)
open import Fragment.Algebra.FreeAlgebra using (subst)

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-isSemigroup)
open import Data.Fin using (Fin; zero; suc; #_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Function using (_∘_)

open import Fragment.Macros.Fin
open import Fragment.Macros.Destructure

open import Algebra.Structures using (IsSemigroup)

+-isModel : IsModel Θ-semigroup (PE.setoid ℕ)
+-isModel = semigroup→isModel (PE.setoid ℕ) +-isSemigroup

+-model : Model Θ-semigroup
+-model = record { isModel = +-isModel; Carrierₛ = PE.setoid ℕ }

open import Fragment.Extensions.Semigroup +-isModel 2

{- (m ++ 2 ∷ []) ++ (3 ∷ [] ++ n) -}
{- (m ∷ [] ++ 2 ∷ []) ++ (3 ∷ [] ++ n ∷ []) -}
{- (0 ∷ m ++ 2 ∷ []) ++ (3 ∷ [] ++ 0 ∷ n) -}

module _ {m n : ℕ} where
  lhs-α : Fin 4 → NormalSemigroup
  lhs-α zero                   = ++-inr-θ (# 0)
  lhs-α (suc zero)             = ++-inl 2
  lhs-α (suc (suc zero))       = ++-inl 3
  lhs-α (suc (suc (suc zero))) = ++-inr-θ (# 1)

  lhs-ω : Fin 4 → ℕ
  lhs-ω = direct-subst +-model ((m + 2) + (3 + n))

  lhs : NormalSemigroup
  lhs = subst ++-algebra lhs-α (destruct +-model ((m + 2) + (3 + n)))

  rhs-α : Fin 3 → NormalSemigroup
  rhs-α zero             = ++-inr-θ (# 0)
  rhs-α (suc zero)       = ++-inl 5
  rhs-α (suc (suc zero)) = ++-inr-θ (# 1)

  rhs-ω : Fin 3 → ℕ
  rhs-ω = direct-subst +-model ((m + 5) + n)

  rhs : NormalSemigroup
  rhs = subst ++-algebra rhs-α (destruct +-model ((m + 5) + n))

  θ : Fin 2 → ℕ
  θ zero       = m
  θ (suc zero) = n

  p : reduce ++-isFrex θ lhs ≡ (m + 2) + (3 + n)
  p = factor ++-isFrex lhs-ω lhs-α θ
             (fin-refl 4 ((reduce ++-isFrex θ) ∘ lhs-α) lhs-ω)
             {x = destruct +-model ((m + 2) + (3 + n))}

  q : reduce ++-isFrex θ rhs ≡ (m + 5) + n
  q = factor ++-isFrex rhs-ω rhs-α θ
             (fin-refl 3 ((reduce ++-isFrex θ) ∘ rhs-α) rhs-ω)
             {x = destruct +-model ((m + 5) + n)}

  simple : (m + 2) + (3 + n) ≡ (m + 5) + n
  simple = fundamental ++-isFrex {x' = lhs} {y' = rhs} θ p q PE.refl
