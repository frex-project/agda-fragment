{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Coproduct {Θ : Theory} where

open import Fragment.Equational.Model

open import Level using (Level; Setω)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

-- FIXME duplicates code in Fragment.Algebra.Coproduct

module _
  (M : Model Θ {a} {ℓ₁})
  (N : Model Θ {b} {ℓ₂})
  (M+N : Model Θ {c} {ℓ₃})
  where

  open Model M renaming (Carrierₐ to S)
  open Model N renaming (Carrierₐ to T)
  open Model M+N renaming (Carrierₐ to S+T)

  open import Fragment.Algebra.Homomorphism (Σ Θ)
  open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ) using (_≡ₕ_)

  record IsCoproduct : Setω where
    field
      inl : S →ₕ S+T
      inr : T →ₕ S+T

      [_,_] : ∀ {d ℓ₄} {W : Model Θ {d} {ℓ₄}}
              → S →ₕ Model.Carrierₐ W
              → T →ₕ Model.Carrierₐ W
              → S+T →ₕ Model.Carrierₐ W

      commute₁ : ∀ {d ℓ₄} {W : Model Θ {d} {ℓ₄}}
                 → {F : S →ₕ Model.Carrierₐ W}
                 → {G : T →ₕ Model.Carrierₐ W}
                 → ([_,_] {W = W} F G) ∘ₕ inl ≡ₕ F

      commute₂ : ∀ {d ℓ₄} {W : Model Θ {d} {ℓ₄}}
                 → {F : S →ₕ Model.Carrierₐ W}
                 → {G : T →ₕ Model.Carrierₐ W}
                 → ([_,_] {W = W} F G) ∘ₕ inr ≡ₕ G

      universal : ∀ {d ℓ₄} {W : Model Θ {d} {ℓ₄}}
                  → {F : S →ₕ Model.Carrierₐ W}
                  → {G : T →ₕ Model.Carrierₐ W}
                  → {H : S+T →ₕ Model.Carrierₐ W}
                  → H ∘ₕ inl ≡ₕ F
                  → H ∘ₕ inr ≡ₕ G
                  → ([_,_] {W = W} F G) ≡ₕ H
