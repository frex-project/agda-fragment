{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.CSemigroup.Arith.Functions where

open import Fragment.Examples.CSemigroup.Arith.Base

-- Fully dynamic associativity

+-dyn-assoc₁ : ∀ {f : ℕ → ℕ} {m n o} → (f m + n) + o ≡ f m + (n + o)
+-dyn-assoc₁ = fragment CSemigroupFrex +-csemigroup

+-dyn-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → ((f m + n) + o) + g p ≡ f m + (n + (o + g p))
+-dyn-assoc₂ = fragment CSemigroupFrex +-csemigroup

+-dyn-assoc₃ : ∀ {f g h : ℕ → ℕ} {m n o p q} → (f m + n) + g o + (p + h q) ≡ f m + (n + g o + p) + h q
+-dyn-assoc₃ = fragment CSemigroupFrex +-csemigroup

*-dyn-assoc₁ : ∀ {f : ℕ → ℕ} {m n o} → (f m * n) * o ≡ f m * (n * o)
*-dyn-assoc₁ = fragment CSemigroupFrex *-csemigroup

*-dyn-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → ((f m * n) * o) * g p ≡ f m * (n * (o * g p))
*-dyn-assoc₂ = fragment CSemigroupFrex *-csemigroup

*-dyn-assoc₃ : ∀ {f g h : ℕ → ℕ} {m n o p q} → (f m * n) * g o * (p * h q) ≡ f m * (n * g o * p) * h q
*-dyn-assoc₃ = fragment CSemigroupFrex *-csemigroup

-- Fully dynamic commutativity

+-dyn-comm₁ : ∀ {f : ℕ → ℕ} {m} → f m + m ≡ m + f m
+-dyn-comm₁ = fragment CSemigroupFrex +-csemigroup

+-dyn-comm₂ : ∀ {f g : ℕ → ℕ} {m n o} → f m + (n + g o) ≡ (g o + n) + f m
+-dyn-comm₂ = fragment CSemigroupFrex +-csemigroup

+-dyn-comm₃ : ∀ {f g h : ℕ → ℕ} {m n o p} → (f m + g n) + (h o + p) ≡ (p + h o) + (g n + f m)
+-dyn-comm₃ = fragment CSemigroupFrex +-csemigroup

*-dyn-comm₁ : ∀ {f : ℕ → ℕ} {m} → f m * m ≡ m * f m
*-dyn-comm₁ = fragment CSemigroupFrex *-csemigroup

*-dyn-comm₂ : ∀ {f g : ℕ → ℕ} {m n o} → f m * (n * g o) ≡ (g o * n) * f m
*-dyn-comm₂ = fragment CSemigroupFrex *-csemigroup

*-dyn-comm₃ : ∀ {f g h : ℕ → ℕ} {m n o p} → (f m * g n) * (h o * p) ≡ (p * h o) * (g n * f m)
*-dyn-comm₃ = fragment CSemigroupFrex *-csemigroup

-- Fully dynamic associavity and commutativity

+-dyn-comm-assoc₁ : ∀ {f : ℕ → ℕ} {m} → (f m + f (f m)) + f (f (f m)) ≡ f (f (f m)) + (f (f m) + f m)
+-dyn-comm-assoc₁ = fragment CSemigroupFrex +-csemigroup

+-dyn-comm-assoc₂ : ∀ {f g : ℕ → ℕ} {m n} → ((f m + f n) + g m) + g n ≡ g m + (f n + (g n + f m))
+-dyn-comm-assoc₂ = fragment CSemigroupFrex +-csemigroup

+-dyn-comm-assoc₃ : ∀ {f : ℕ → ℕ} {m n o p q} → f (m + n) + o + (p + q) ≡ f (m + n) + q + (p + o)
+-dyn-comm-assoc₃ = fragment CSemigroupFrex +-csemigroup

*-dyn-comm-assoc₁ : ∀ {f : ℕ → ℕ} {m} → (f m * f (f m)) * f (f (f m)) ≡ f (f (f m)) * (f (f m) * f m)
*-dyn-comm-assoc₁ = fragment CSemigroupFrex *-csemigroup

*-dyn-comm-assoc₂ : ∀ {f g : ℕ → ℕ} {m n} → ((f m * f n) * g m) * g n ≡ g m * (f n * (g n * f m))
*-dyn-comm-assoc₂ = fragment CSemigroupFrex *-csemigroup

*-dyn-comm-assoc₃ : ∀ {f : ℕ → ℕ} {m n o p q} → f (m + n) * o * (p * q) ≡ f (m + n) * q * (p * o)
*-dyn-comm-assoc₃ = fragment CSemigroupFrex *-csemigroup

-- Partially static associativity

+-sta-assoc₁ : ∀ {f : ℕ → ℕ} {m} → (m + 2) + (3 + f 0) ≡ m + (5 + f 0)
+-sta-assoc₁ = fragment CSemigroupFrex +-csemigroup

+-sta-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → (((f m + g n) + 5) + o) + p ≡ f m + (g n + (2 + (3 + (o + p))))
+-sta-assoc₂ = fragment CSemigroupFrex +-csemigroup

+-sta-assoc₃ : ∀ {f : ℕ → ℕ} {m n o p} → f (n + m) + (n + 2) + (3 + (o + p)) ≡ (((n + 1) + (4 + o)) + p) + f (n + m)
+-sta-assoc₃ = fragment CSemigroupFrex +-csemigroup

*-sta-assoc₁ : ∀ {f : ℕ → ℕ} {m} → (m * 2) * (3 * f 0) ≡ m * (6 * f 0)
*-sta-assoc₁ = fragment CSemigroupFrex *-csemigroup

*-sta-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → (((f m * g n) * 6) * o) * p ≡ f m * (g n * (2 * (3 * (o * p))))
*-sta-assoc₂ = fragment CSemigroupFrex *-csemigroup

*-sta-assoc₃ : ∀ {f : ℕ → ℕ} {m n o p} → f (n + m) * (n * 4) * (3 * (o * p)) ≡ (((n * 2) * (6 * o)) * p) * f (n + m)
*-sta-assoc₃ = fragment CSemigroupFrex *-csemigroup

-- Partially static commutativity

+-sta-comm₁ : ∀ {f g : ℕ → ℕ} {m} → f m + g 1 ≡ g 1 + f m
+-sta-comm₁ = fragment CSemigroupFrex +-csemigroup

+-sta-comm₂ : ∀ {f g : ℕ → ℕ} {m n} → f m + (2 + g n) ≡ (g n + 2) + f m
+-sta-comm₂ = fragment CSemigroupFrex +-csemigroup

+-sta-comm₃ : ∀ {f g h : ℕ → ℕ} {m n o p} → (1 + (f m + g n)) + ((o + p) + h 2) ≡ ((p + o) + h 2) + (1 + (g n + f m))
+-sta-comm₃ = fragment CSemigroupFrex +-csemigroup

*-sta-comm₁ : ∀ {f g : ℕ → ℕ} {m} → f m * g 1 ≡ g 1 * f m
*-sta-comm₁ = fragment CSemigroupFrex *-csemigroup

*-sta-comm₂ : ∀ {f g : ℕ → ℕ} {m n} → f m * (2 * g n) ≡ (g n * 2) * f m
*-sta-comm₂ = fragment CSemigroupFrex *-csemigroup

*-sta-comm₃ : ∀ {f g h : ℕ → ℕ} {m n o p} → (3 * (f m * g n)) * ((o * p) * h 2) ≡ ((p * o) * h 2) * (3 * (g n * f m))
*-sta-comm₃ = fragment CSemigroupFrex *-csemigroup

-- Partially static associavity and commutativity

+-sta-comm-assoc₁ : ∀ {f : ℕ → ℕ} {m n o} → 1 + (f m + n) + f o + 4 ≡ 5 + n + (f m + f o)
+-sta-comm-assoc₁ = fragment CSemigroupFrex +-csemigroup

+-sta-comm-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → 5 + ((f m + n) + o) + g p ≡ g p + ((o + 1) + (n + f m)) + 4
+-sta-comm-assoc₂ = fragment CSemigroupFrex +-csemigroup

+-sta-comm-assoc₃ : ∀ {f g h : ℕ → ℕ} {m n o p q} → (f m + g n + 1) + o + (p + h q + 4) ≡ (2 + h q) + (p + o + g n) + (f m + 3)
+-sta-comm-assoc₃ = fragment CSemigroupFrex +-csemigroup

*-sta-comm-assoc₁ : ∀ {f : ℕ → ℕ} {m n o} → 2 * (f m * n) * f o * 6 ≡ 12 * n * (f m * f o)
*-sta-comm-assoc₁ = fragment CSemigroupFrex *-csemigroup

*-sta-comm-assoc₂ : ∀ {f g : ℕ → ℕ} {m n o p} → 12 * ((f m * n) * o) * g p ≡ g p * ((o * 2) * (n * f m)) * 6
*-sta-comm-assoc₂ = fragment CSemigroupFrex *-csemigroup

*-sta-comm-assoc₃ : ∀ {f g h : ℕ → ℕ} {m n o p q} → (f m * g n * 2) * o * (p * h q * 6) ≡ (4 * h q) * (p * o * g n) * (f m * 3)
*-sta-comm-assoc₃ = fragment CSemigroupFrex *-csemigroup
