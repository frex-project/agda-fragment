{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Coproduct (Σ : Signature) where

open import Fragment.Algebra.Algebra

open import Level using (Level; Setω)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  (S : Algebra Σ {a} {ℓ₁})
  (T : Algebra Σ {b} {ℓ₂})
  (S+T : Algebra Σ {c} {ℓ₃})
  where

  open import Fragment.Algebra.Homomorphism Σ
  open import Fragment.Algebra.Homomorphism.Setoid Σ using (_≡ₕ_)

  record IsCoproduct : Setω where
    field
      inl : S →ₕ S+T
      inr : T →ₕ S+T

      [_,_] : ∀ {d ℓ₄} {W : Algebra Σ {d} {ℓ₄}}
              → S →ₕ W → T →ₕ W → S+T →ₕ W

      commute₁ : ∀ {d ℓ₄} {W : Algebra Σ {d} {ℓ₄}}
                 → {F : S →ₕ W} {G : T →ₕ W}
                 → [ F , G ] ∘ₕ inl ≡ₕ F

      commute₂ : ∀ {d ℓ₄} {W : Algebra Σ {d} {ℓ₄}}
                 → {F : S →ₕ W} {G : T →ₕ W}
                 → [ F , G ] ∘ₕ inr ≡ₕ G

      universal : ∀ {d ℓ₄} {W : Algebra Σ {d} {ℓ₄}}
                  → {F : S →ₕ W} {G : T →ₕ W} {H : S+T →ₕ W}
                  → H ∘ₕ inl ≡ₕ F
                  → H ∘ₕ inr ≡ₕ G
                  → [ F , G ] ≡ₕ H
