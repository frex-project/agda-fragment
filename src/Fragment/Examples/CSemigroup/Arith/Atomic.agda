{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.CSemigroup.Arith.Atomic where

open import Fragment.Examples.CSemigroup.Arith.Base

-- Fully dynamic associativity

+-dyn-assoc₁ : ∀ {m n o} → (m + n) + o ≡ m + (n + o)
+-dyn-assoc₁ = fragment CSemigroupFrex +-csemigroup

+-dyn-assoc₂ : ∀ {m n o p} → ((m + n) + o) + p ≡ m + (n + (o + p))
+-dyn-assoc₂ = fragment CSemigroupFrex +-csemigroup

+-dyn-assoc₃ : ∀ {m n o p q} → (m + n) + o + (p + q) ≡ m + (n + o + p) + q
+-dyn-assoc₃ = fragment CSemigroupFrex +-csemigroup

*-dyn-assoc₁ : ∀ {m n o} → (m * n) * o ≡ m * (n * o)
*-dyn-assoc₁ = fragment CSemigroupFrex *-csemigroup

*-dyn-assoc₂ : ∀ {m n o p} → ((m * n) * o) * p ≡ m * (n * (o * p))
*-dyn-assoc₂ = fragment CSemigroupFrex *-csemigroup

*-dyn-assoc₃ : ∀ {m n o p q} → (m * n) * o * (p * q) ≡ m * (n * o * p) * q
*-dyn-assoc₃ = fragment CSemigroupFrex *-csemigroup

-- Fully dynamic commutativity

+-dyn-comm₁ : ∀ {m n} → m + n ≡ n + m
+-dyn-comm₁ = fragment CSemigroupFrex +-csemigroup

+-dyn-comm₂ : ∀ {m n o} → m + (n + o) ≡ (o + n) + m
+-dyn-comm₂ = fragment CSemigroupFrex +-csemigroup

+-dyn-comm₃ : ∀ {m n o p} → (m + n) + (o + p) ≡ (p + o) + (n + m)
+-dyn-comm₃ = fragment CSemigroupFrex +-csemigroup

*-dyn-comm₁ : ∀ {m n} → m * n ≡ n * m
*-dyn-comm₁ = fragment CSemigroupFrex *-csemigroup

*-dyn-comm₂ : ∀ {m n o} → m * (n * o) ≡ (o * n) * m
*-dyn-comm₂ = fragment CSemigroupFrex *-csemigroup

*-dyn-comm₃ : ∀ {m n o p} → (m * n) * (o * p) ≡ (p * o) * (n * m)
*-dyn-comm₃ = fragment CSemigroupFrex *-csemigroup

-- Fully dynamic associavity and commutativity

+-dyn-comm-assoc₁ : ∀ {m n o} → (m + n) + o ≡ n + (m + o)
+-dyn-comm-assoc₁ = fragment CSemigroupFrex +-csemigroup

+-dyn-comm-assoc₂ : ∀ {m n o p} → ((m + n) + o) + p ≡ p + (o + (n + m))
+-dyn-comm-assoc₂ = fragment CSemigroupFrex +-csemigroup

+-dyn-comm-assoc₃ : ∀ {m n o p q} → (m + n) + o + (p + q) ≡ q + (p + o + n) + m
+-dyn-comm-assoc₃ = fragment CSemigroupFrex +-csemigroup

*-dyn-comm-assoc₁ : ∀ {m n o} → (m * n) * o ≡ n * (m * o)
*-dyn-comm-assoc₁ = fragment CSemigroupFrex *-csemigroup

*-dyn-comm-assoc₂ : ∀ {m n o p} → ((m * n) * o) * p ≡ p * (o * (n * m))
*-dyn-comm-assoc₂ = fragment CSemigroupFrex *-csemigroup

*-dyn-comm-assoc₃ : ∀ {m n o p q} → (m * n) * o * (p * q) ≡ q * (p * o * n) * m
*-dyn-comm-assoc₃ = fragment CSemigroupFrex *-csemigroup

-- Partially static associativity

+-sta-assoc₁ : ∀ {m n} → (m + 2) + (3 + n) ≡ m + (5 + n)
+-sta-assoc₁ = fragment CSemigroupFrex +-csemigroup

+-sta-assoc₂ : ∀ {m n o p} → (((m + n) + 5) + o) + p ≡ m + (n + (2 + (3 + (o + p))))
+-sta-assoc₂ = fragment CSemigroupFrex +-csemigroup

+-sta-assoc₃ : ∀ {m n o p} → ((m + n) + 2) + (3 + (o + p)) ≡ m + ((n + 1) + (4 + o)) + p
+-sta-assoc₃ = fragment CSemigroupFrex +-csemigroup

*-sta-assoc₁ : ∀ {m n} → (m * 2) * (3 * n) ≡ m * (6 * n)
*-sta-assoc₁ = fragment CSemigroupFrex *-csemigroup

*-sta-assoc₂ : ∀ {m n o p} → (((m * n) * 6) * o) * p ≡ m * (n * (2 * (3 * (o * p))))
*-sta-assoc₂ = fragment CSemigroupFrex *-csemigroup

*-sta-assoc₃ : ∀ {m n o p} → ((m * n) * 2) * (6 * (o * p)) ≡ m * ((n * 2) * (6 * o)) * p
*-sta-assoc₃ = fragment CSemigroupFrex *-csemigroup

-- Partially static commutativity

+-sta-comm₁ : ∀ {m} → m + 1 ≡ 1 + m
+-sta-comm₁ = fragment CSemigroupFrex +-csemigroup

+-sta-comm₂ : ∀ {m n} → m + (2 + n) ≡ (n + 2) + m
+-sta-comm₂ = fragment CSemigroupFrex +-csemigroup

+-sta-comm₃ : ∀ {m n o p} → (1 + (m + n)) + ((o + p) + 2) ≡ ((p + o) + 2) + (1 + (n + m))
+-sta-comm₃ = fragment CSemigroupFrex +-csemigroup

*-sta-comm₁ : ∀ {m} → m * 4 ≡ 4 * m
*-sta-comm₁ = fragment CSemigroupFrex *-csemigroup

*-sta-comm₂ : ∀ {m n} → m * (2 * n) ≡ (n * 2) * m
*-sta-comm₂ = fragment CSemigroupFrex *-csemigroup

*-sta-comm₃ : ∀ {m n o p} → (4 * (m * n)) * ((o * p) * 2) ≡ ((p * o) * 2) * (4 * (n * m))
*-sta-comm₃ = fragment CSemigroupFrex *-csemigroup

-- Partially static associavity and commutativity

+-sta-comm-assoc₁ : ∀ {m n o} → 1 + (m + n) + o + 4 ≡ 5 + n + (m + o)
+-sta-comm-assoc₁ = fragment CSemigroupFrex +-csemigroup

+-sta-comm-assoc₂ : ∀ {m n o p} → 5 + ((m + n) + o) + p ≡ p + ((o + 1) + (n + m)) + 4
+-sta-comm-assoc₂ = fragment CSemigroupFrex +-csemigroup

+-sta-comm-assoc₃ : ∀ {m n o p q} → (m + n + 1) + o + (p + q + 4) ≡ (2 + q) + (p + o + n) + (m + 3)
+-sta-comm-assoc₃ = fragment CSemigroupFrex +-csemigroup

*-sta-comm-assoc₁ : ∀ {m n o} → 2 * (m * n) * o * 3 ≡ 6 * n * (m * o)
*-sta-comm-assoc₁ = fragment CSemigroupFrex *-csemigroup

*-sta-comm-assoc₂ : ∀ {m n o p} → 6 * ((m * n) * o) * p ≡ p * ((o * 2) * (n * m)) * 3
*-sta-comm-assoc₂ = fragment CSemigroupFrex *-csemigroup

*-sta-comm-assoc₃ : ∀ {m n o p q} → (m * n * 3) * o * (p * q * 4) ≡ (2 * q) * (p * o * n) * (m * 6)
*-sta-comm-assoc₃ = fragment CSemigroupFrex *-csemigroup
