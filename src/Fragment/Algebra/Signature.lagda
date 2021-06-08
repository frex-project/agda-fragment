\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.Signature where

open import Data.Nat using (ℕ)
\end{code}

%<*signature>
\begin{code}
record Signature : Set₁ where
  field
    ops : ℕ → Set
\end{code}
%</signature>

\begin{code}[hidden]
open Signature public

data ExtendedOp (Σ : Signature) (O : ℕ → Set) : ℕ → Set where
  new : ∀ {n} → O n → ExtendedOp Σ O n
  old : ∀ {n} → ops Σ n → ExtendedOp Σ O n

_⦅_⦆ : (Σ : Signature) → (ℕ → Set) → Signature
Σ ⦅ O ⦆ = record { ops = ExtendedOp Σ O }
\end{code}
