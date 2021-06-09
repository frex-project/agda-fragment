\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory.Bundles where

open import Fragment.Algebra.Signature
open import Fragment.Equational.Theory.Base
open import Fragment.Equational.Theory.Combinators

open import Data.Nat using (ℕ)
\end{code}

%<*magma>
\begin{code}
data MagmaOp : ℕ → Set where
  • : MagmaOp 2

Σ-magma : Signature
Σ-magma = record { ops = MagmaOp }
\end{code}
%</magma>

\begin{code}[hidden]
import Fragment.Equational.Theory.Laws Σ-magma as L

data MagmaEq : ℕ → Set where

magma-eqs : ∀ {n} → MagmaEq n → Eq Σ-magma n
magma-eqs ()

data SemigroupEq : ℕ → Set where
  assoc : SemigroupEq 3

semigroup-eqs : ∀ {n} → SemigroupEq n → Eq Σ-magma n
semigroup-eqs assoc = L.assoc •
\end{code}

%<*csemigroupeqs>
\begin{code}
data CSemigroupEq : ℕ → Set where
  comm  : CSemigroupEq 2
  assoc : CSemigroupEq 3
\end{code}
%</csemigroupeqs>

%<*csemigroupinterp>
\begin{code}
csemigroup-eqs : ∀ {n} → CSemigroupEq n → Eq Σ-magma n
csemigroup-eqs comm  = L.comm •
csemigroup-eqs assoc = L.assoc •
\end{code}
%</csemigroupinterp>

\begin{code}[hidden]
Θ-magma : Theory
Θ-magma = record { Σ     = Σ-magma
                 ; eqs   = MagmaEq
                 ; _⟦_⟧ₑ = magma-eqs
                 }

Θ-semigroup : Theory
Θ-semigroup = record { Σ     = Σ-magma
                     ; eqs   = SemigroupEq
                     ; _⟦_⟧ₑ = semigroup-eqs
                     }
\end{code}

%<*csemigrouptheory>
\begin{code}
Θ-csemigroup : Theory
Θ-csemigroup = record { Σ     = Σ-magma
                      ; eqs   = CSemigroupEq
                      ; _⟦_⟧ₑ = csemigroup-eqs
                      }
\end{code}
%</csemigrouptheory>

\begin{code}[hidden]
Θ-monoid : Theory
Θ-monoid = AddId Θ-semigroup •

Θ-cmonoid : Theory
Θ-cmonoid = AddId Θ-csemigroup •
\end{code}
