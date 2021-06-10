\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.Semigroup.Arith.Reasoning where

open import Fragment.Examples.Semigroup.Arith.Base

+-direct : ∀ {m n} → (m + 2) + (3 + n) ≡ m + (5 + n)
+-direct {m} {n} = begin
    (m + 2) + (3 + n)
  ≡⟨ fragment SemigroupFrex +-semigroup ⟩
    m + (5 + n)
  ∎

open import Data.Nat.Properties using (*-distribˡ-+)
\end{code}

%<*reason>
\begin{code}
+-inner : ∀ {m n k} → k * (m + 2) + k * (3 + n) ≡ k * (m + 5 + n)
+-inner {m} {n} {k} = begin
    k * (m + 2) + k * (3 + n)
  ≡⟨ sym (*-distribˡ-+ k (m + 2) (3 + n)) ⟩
    k * ((m + 2) + (3 + n))
  ≡⟨ cong (k *_) (fragment SemigroupFrex +-semigroup) ⟩
    k * (m + 5 + n)
  ∎
\end{code}
%</reason>
