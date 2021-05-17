{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.Semigroup.Arith.Atomic where

open import Fragment.Examples.Semigroup.Arith.Base

-- Fully dynamic associativity

dyn-assoc₁ : ∀ {m n o} → (m + n) + o ≡ m + (n + o)
dyn-assoc₁ = fragment SemigroupFrex +-semigroup

dyn-assoc₂ : ∀ {m n o p} → ((m + n) + o) + p ≡ m + (n + (o + p))
dyn-assoc₂ = fragment SemigroupFrex +-semigroup

dyn-assoc₃ : ∀ {m n o p q} → (m + n) + o + (p + q) ≡ m + (n + o + p) + q
dyn-assoc₃ = fragment SemigroupFrex +-semigroup

-- Partially static associativity

sta-assoc₁ : ∀ {m n} → (m + 2) + (3 + n) ≡ m + (5 + n)
sta-assoc₁ = fragment SemigroupFrex +-semigroup

sta-assoc₂ : ∀ {m n o p} → (((m + n) + 5) + o) + p ≡ m + (n + (2 + (3 + (o + p))))
sta-assoc₂ = fragment SemigroupFrex +-semigroup

sta-assoc₃ : ∀ {m n o p} → ((m + n) + 2) + (3 + (o + p)) ≡ m + ((n + 1) + (4 + o)) + p
sta-assoc₃ = fragment SemigroupFrex +-semigroup
