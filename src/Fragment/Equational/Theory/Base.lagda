\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Theory.Base where

open import Function using (_∘_)

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Free
open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Properties

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; map)
\end{code}

%<*equation>
\begin{code}
Eq : (Σ : Signature) → (n : ℕ) → Set
Eq Σ n = ∥ F Σ n ∥ × ∥ F Σ n ∥
\end{code}
%</equation>

%<*theory>
\begin{code}
record Theory : Set₁ where
  field
    Σ     : Signature
    eqs   : ℕ → Set
    _⟦_⟧ₑ : ∀ {arity} → eqs arity → Eq Σ arity
\end{code}
%</theory>

\begin{code}[hidden]
  open Signature Σ

open Theory public

data ExtendedEq (Θ : Theory) (E : ℕ → Set) : ℕ → Set where
  new : ∀ {n} → E n → ExtendedEq Θ E n
  old : ∀ {n} → eqs Θ n → ExtendedEq Θ E n

_⦅_⦆ₒ : (Θ : Theory) → (O : ℕ → Set) → Theory
Θ ⦅ O ⦆ₒ = record { Σ     = (Σ Θ) ⦅ O ⦆
                  ; eqs   = eqs Θ
                  ; _⟦_⟧ₑ = (map extend extend) ∘ Θ ⟦_⟧ₑ
                  }

_⦅_/_⦆ : (Θ : Theory)
         → (E : ℕ → Set)
         → (∀ {n} → E n → Eq (Σ Θ) n)
         → Theory
Θ ⦅ E / ⟦_⟧' ⦆ = record { Σ     = Σ Θ
                        ; eqs   = ExtendedEq Θ E
                        ; _⟦_⟧ₑ = withE
                        }
  where withE : ∀ {n} → ExtendedEq Θ E n → Eq (Σ Θ) n
        withE (new eq) = ⟦ eq ⟧'
        withE (old eq) = Θ ⟦ eq ⟧ₑ

_⦅_∣_/_⦆ : (Θ : Theory)
           → (O : ℕ → Set)
           → (E : ℕ → Set)
           → (∀ {n} → E n → Eq ((Σ Θ) ⦅ O ⦆) n)
           → Theory
Θ ⦅ O ∣ E / ⟦_⟧' ⦆ = (Θ ⦅ O ⦆ₒ) ⦅ E / ⟦_⟧' ⦆
\end{code}
