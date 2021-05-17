{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.Semigroup.Arith.Functions where

open import Fragment.Examples.Semigroup.Arith.Base

-- Fully dynamic associativity

+-dyn-assoc₁ : ∀ {f : ℕ → ℕ} {m n o} → (f m + n) + o ≡ f m + (n + o)
+-dyn-assoc₁ = fragment SemigroupFrex +-semigroup

+-dyn-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → ((f m + n) + o) + g p ≡ f m + (n + (o + g p))
+-dyn-assoc₂ = fragment SemigroupFrex +-semigroup

+-dyn-assoc₃ : ∀ {f g h : ℕ → ℕ} {m n o p q} → (f m + n) + g o + (p + h q) ≡ f m + (n + g o + p) + h q
+-dyn-assoc₃ = fragment SemigroupFrex +-semigroup

*-dyn-assoc₁ : ∀ {f : ℕ → ℕ} {m n o} → (f m * n) * o ≡ f m * (n * o)
*-dyn-assoc₁ = fragment SemigroupFrex *-semigroup

*-dyn-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → ((f m * n) * o) * g p ≡ f m * (n * (o * g p))
*-dyn-assoc₂ = fragment SemigroupFrex *-semigroup

*-dyn-assoc₃ : ∀ {f g h : ℕ → ℕ} {m n o p q} → (f m * n) * g o * (p * h q) ≡ f m * (n * g o * p) * h q
*-dyn-assoc₃ = fragment SemigroupFrex *-semigroup

-- Partially static associativity

+-sta-assoc₁ : ∀ {f : ℕ → ℕ} {m} → (m + 2) + (3 + f 0) ≡ m + (5 + f 0)
+-sta-assoc₁ = fragment SemigroupFrex +-semigroup

+-sta-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → (((f m + g n) + 5) + o) + p ≡ f m + (g n + (2 + (3 + (o + p))))
+-sta-assoc₂ = fragment SemigroupFrex +-semigroup

+-sta-assoc₃ : ∀ {f : ℕ → ℕ} {m n o p} → f (n + m) + (n + 2) + (3 + (o + p)) ≡ f (n + m) + (((n + 1) + (4 + o)) + p)
+-sta-assoc₃ = fragment SemigroupFrex +-semigroup

*-sta-assoc₁ : ∀ {f : ℕ → ℕ} {m} → (m * 2) * (3 * f 0) ≡ m * (6 * f 0)
*-sta-assoc₁ = fragment SemigroupFrex *-semigroup

*-sta-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → (((f m * g n) * 6) * o) * p ≡ f m * (g n * (2 * (3 * (o * p))))
*-sta-assoc₂ = fragment SemigroupFrex *-semigroup

*-sta-assoc₃ : ∀ {f : ℕ → ℕ} {m n o p} → f (n + m) * (n * 4) * (3 * (o * p)) ≡ f (n + m) * (((n * 2) * (6 * o)) * p)
*-sta-assoc₃ = fragment SemigroupFrex *-semigroup
