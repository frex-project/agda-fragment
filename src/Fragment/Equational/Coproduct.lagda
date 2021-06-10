\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Coproduct (Θ : Theory) where

open import Fragment.Equational.Model Θ
open import Fragment.Algebra.Homomorphism (Σ Θ)

open import Level using (Level; Setω)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  (A : Model {a} {ℓ₁})
  (B : Model {b} {ℓ₂})
  (A+B : Model {c} {ℓ₃})
  where
\end{code}
%<*coproduct>
\begin{code}
  record IsCoproduct : Setω where
    field
      inl : ∥ A ∥ₐ ⟿ ∥ A+B ∥ₐ
      inr : ∥ B ∥ₐ ⟿ ∥ A+B ∥ₐ

      _[_,_] : ∀ {d ℓ₄} (X : Model {d} {ℓ₄})
               → ∥ A ∥ₐ ⟿ ∥ X ∥ₐ
               → ∥ B ∥ₐ ⟿ ∥ X ∥ₐ
               → ∥ A+B ∥ₐ ⟿ ∥ X ∥ₐ
\end{code}
%</coproduct>
\begin{code}[hidden]
      commute₁ : ∀ {d ℓ₄} {X : Model {d} {ℓ₄}}
                 → {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
                 → {g : ∥ B ∥ₐ ⟿ ∥ X ∥ₐ}
                 → X [ f , g ] ⊙ inl ≗ f

      commute₂ : ∀ {d ℓ₄} {X : Model {d} {ℓ₄}}
                 → {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
                 → {g : ∥ B ∥ₐ ⟿ ∥ X ∥ₐ}
                 → X [ f , g ] ⊙ inr ≗ g

      universal : ∀ {d ℓ₄} {X : Model {d} {ℓ₄}}
                  → {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
                  → {g : ∥ B ∥ₐ ⟿ ∥ X ∥ₐ}
                  → {h : ∥ A+B ∥ₐ ⟿ ∥ X ∥ₐ}
                  → h ⊙ inl ≗ f
                  → h ⊙ inr ≗ g
                  → X [ f , g ] ≗ h
\end{code}
