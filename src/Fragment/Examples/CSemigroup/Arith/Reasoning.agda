{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.CSemigroup.Arith.Reasoning where

open import Fragment.Examples.CSemigroup.Arith.Base

+-direct : ∀ {m n} → (m + 2) + (3 + n) ≡ m + (n + 5)
+-direct {m} {n} = begin
    (m + 2) + (3 + n)
  ≡⟨ fragment CSemigroupFrex +-csemigroup ⟩
    m + (n + 5)
  ∎

open import Data.Nat.Properties using (*-distribˡ-+)

+-inner : ∀ {m n k} → k * (m + 2) + k * (3 + n) ≡ (m + n + 5) * k
+-inner {m} {n} {k} = begin
    k * (m + 2) + k * (3 + n)
  ≡⟨ sym (*-distribˡ-+ k (m + 2) (3 + n)) ⟩
    k * ((m + 2) + (3 + n))
  ≡⟨ cong (k *_) (fragment CSemigroupFrex +-csemigroup) ⟩
    k * (m + n + 5)
  ≡⟨ fragment CSemigroupFrex *-csemigroup ⟩
    (m + n + 5) * k
  ∎
