\begin{code}[hidden]
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning
\end{code}

%<*simple>
\begin{code}
simple : ∀ x y → x + (2 + (3 + y)) ≡ x + (5 + y)
simple x y = refl
\end{code}
%</simple>

%<*variation1>
\begin{code}
variation₁ : ∀ x y → (x + 2) + (3 + y) ≡ x + (5 + y)
variation₁ x y = +-assoc x 2 (3 + y)
\end{code}
%</variation1>

%<*variation2>
\begin{code}
variation₂ : ∀ x y → (2 + x) + (y + 3) ≡ x + (y + 5)
variation₂ x y = begin
    (2 + x) + (y + 3)
  ≡⟨ cong₂ _+_ (+-comm 2 x) (+-comm y 3) ⟩
    (x + 2) + (3 + y)
  ≡⟨ +-assoc x 2 (3 + y) ⟩
    x + (5 + y)
  ≡⟨ cong₂ _+_ refl (+-comm 5 y) ⟩
    x + (y + 5)
  ∎
\end{code}
%</variation2>

%<*automated>
\begin{code}
import Algebra.Solver.Ring.NaturalCoefficients.Default as Solver

automated : ∀ x y → (2 + x) + (y + 3) ≡ x + (y + 5)
automated = solve 2 (λ x y → (con 2 :+ x) :+ (y :+ con 3) :=
                              x :+ (y :+ con 5))
                    refl
  where open Solver +-*-commutativeSemiring
\end{code}
%</automated>

%<*reflection>
\begin{code}
reflection : ∀ x y → (2 + x) + (y + 3) ≡ x + (y + 5)
reflection = solve-∀
  where open import Data.Nat.Tactic.RingSolver
\end{code}
%</reflection>
