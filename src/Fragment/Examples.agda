{-# OPTIONS --without-K --safe #-}

module Fragment.Examples where

open import Fragment.Equational.Bundles using (Θ-semigroup; Σ-magma; MagmaOp)
open import Fragment.Equational.Model
open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.Structures using (semigroup→isModel)

open import Fragment.Algebra.Homomorphism (Σ-magma)

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-isSemigroup)
open import Data.Vec using ([]; _∷_)
open import Data.Fin using (Fin; zero; suc; #_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

+-isModel : IsModel Θ-semigroup (PE.setoid ℕ)
+-isModel = (semigroup→isModel (PE.setoid ℕ) +-isSemigroup)

open import Fragment.Extensions.Semigroup +-isModel 2

simple : ∀ {m n} → (m + 2) + (3 + n) ≡ (m + 5) + n
simple {m = m} {n = n} = fundamental ++-isFrex {x' = lhs} {y' = rhs} θ p q PE.refl
    where θ : Fin 2 → ℕ
          θ zero       = m
          θ (suc zero) = n
          lhs = (++-inr-θ (# 0) ++ ++-inl 2) ++ (++-inl 3 ++ ++-inr-θ (# 1))
          rhs = (++-inr-θ (# 0) ++ ++-inl 5) ++ (++-inr-θ (# 1))
          p : reduce ++-isFrex θ lhs ≡ (m + 2) + (3 + n)
          p = {!!}
          q : reduce ++-isFrex θ rhs ≡ (m + 5) + n
          q = {!!}
