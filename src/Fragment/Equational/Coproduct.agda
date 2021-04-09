{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Coproduct (Θ : Theory) where

open import Fragment.Equational.Model Θ
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ)

open import Level using (Level; Setω)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  (M : Model {a} {ℓ₁})
  (N : Model {b} {ℓ₂})
  (M+N : Model {c} {ℓ₃})
  where

  record IsCoproduct : Setω where
    field
      inl : ∥ M ∥ₐ →ₕ ∥ M+N ∥ₐ
      inr : ∥ N ∥ₐ →ₕ ∥ M+N ∥ₐ

      [_,_] : ∀ {d ℓ₄} {W : Model {d} {ℓ₄}}
              → ∥ M ∥ₐ →ₕ ∥ W ∥ₐ
              → ∥ N ∥ₐ →ₕ ∥ W ∥ₐ
              → ∥ M+N ∥ₐ →ₕ ∥ W ∥ₐ

      commute₁ : ∀ {d ℓ₄} {W : Model {d} {ℓ₄}}
                 → {f : ∥ M ∥ₐ →ₕ ∥ W ∥ₐ}
                 → {g : ∥ N ∥ₐ →ₕ ∥ W ∥ₐ}
                 → ([_,_] {W = W} f g) ∘ₕ inl ≡ₕ f

      commute₂ : ∀ {d ℓ₄} {W : Model {d} {ℓ₄}}
                 → {f : ∥ M ∥ₐ →ₕ ∥ W ∥ₐ}
                 → {g : ∥ N ∥ₐ →ₕ ∥ W ∥ₐ}
                 → ([_,_] {W = W} f g) ∘ₕ inr ≡ₕ g

      universal : ∀ {d ℓ₄} {W : Model {d} {ℓ₄}}
                  → {f : ∥ M ∥ₐ →ₕ ∥ W ∥ₐ}
                  → {g : ∥ N ∥ₐ →ₕ ∥ W ∥ₐ}
                  → {h : ∥ M+N ∥ₐ →ₕ ∥ W ∥ₐ}
                  → h ∘ₕ inl ≡ₕ f
                  → h ∘ₕ inr ≡ₕ g
                  → ([_,_] {W = W} f g) ≡ₕ h
