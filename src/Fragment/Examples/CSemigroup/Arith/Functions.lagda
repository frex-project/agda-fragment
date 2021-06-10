\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.CSemigroup.Arith.Functions where

open import Fragment.Examples.CSemigroup.Arith.Base
\end{code}

%<*arith>
\begin{code}
frexified : ∀ {x y} → (2 + x) + (y + 3) ≡ x + (y + 5)
frexified = fragment CSemigroupFrex +-csemigroup
\end{code}
%<*/arith>

%<*symbols>
\begin{code}
symbols : ∀ {f : ℕ → ℕ} {x y}
          → (2 + f x) + (y + f 3) + f (f 2) ≡ (1 + f x) + (1 + y) + (f 3 + f (f 2))
symbols = fragment CSemigroupFrex +-csemigroup
\end{code}
%<*/symbols>
