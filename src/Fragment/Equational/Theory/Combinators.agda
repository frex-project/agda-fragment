{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory.Base

module Fragment.Equational.Theory.Combinators (Θ : Theory) where

open import Fragment.Algebra.Signature

open import Level using (Level)

open import Data.Nat using (ℕ)

private
  variable
    a ℓ : Level

data HomOp : ℕ → Set where
  h : HomOp 1

data HomEq : ℕ → Set where
  hom : ∀ {n} → ops (Σ Θ) n → HomEq n

AddHom : Theory
AddHom = Θ ⦅ HomOp ∣ HomEq / hom' ⦆
  where import Fragment.Equational.Theory.Laws ((Σ Θ) ⦅ HomOp ⦆) as L

        hom' : ∀ {arity} → HomEq arity → Eq ((Σ Θ) ⦅ HomOp ⦆) arity
        hom' (hom f) = L.hom (new h) (old f)

data IdOp : ℕ → Set where
  α : IdOp 0

data IdEq : ℕ → Set where
  idₗ : IdEq 1
  idᵣ : IdEq 1

AddId : ops (Σ Θ) 2 → Theory
AddId • = Θ ⦅ IdOp ∣ IdEq / id ⦆
  where import Fragment.Equational.Theory.Laws ((Σ Θ) ⦅ IdOp ⦆) as L

        id : ∀ {arity} → IdEq arity → Eq ((Σ Θ) ⦅ IdOp ⦆) arity
        id idₗ = L.idₗ (new α) (old •)
        id idᵣ = L.idᵣ (new α) (old •)

data AnOp : ℕ → Set where
  α : AnOp 0

data AnEq : ℕ → Set where
  anₗ : AnEq 1
  anᵣ : AnEq 1

AddAn : ops (Σ Θ) 2 → Theory
AddAn • = Θ ⦅ AnOp ∣ AnEq / an ⦆
  where import Fragment.Equational.Theory.Laws ((Σ Θ) ⦅ AnOp ⦆) as L

        an : ∀ {arity} → AnEq arity → Eq ((Σ Θ) ⦅ AnOp ⦆) arity
        an anₗ = L.anₗ (new α) (old •)
        an anᵣ = L.anᵣ (new α) (old •)
