{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Coproduct (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Algebra.Homomorphism.Setoid Σ

open import Level using (Level; Setω)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  (S : Algebra {a} {ℓ₁})
  (T : Algebra {b} {ℓ₂})
  (S+T : Algebra {c} {ℓ₃})
  where

  record IsCoproduct : Setω where
    field
      inl : S →ₕ S+T
      inr : T →ₕ S+T

      [_,_] : ∀ {d ℓ₄} {W : Algebra {d} {ℓ₄}}
              → S →ₕ W → T →ₕ W → S+T →ₕ W

      commute₁ : ∀ {d ℓ₄} {W : Algebra {d} {ℓ₄}}
                 → {f : S →ₕ W} {g : T →ₕ W}
                 → [ f , g ] ∘ₕ inl ≡ₕ f

      commute₂ : ∀ {d ℓ₄} {W : Algebra {d} {ℓ₄}}
                 → {f : S →ₕ W} {g : T →ₕ W}
                 → [ f , g ] ∘ₕ inr ≡ₕ g

      universal : ∀ {d ℓ₄} {W : Algebra {d} {ℓ₄}}
                  → {f : S →ₕ W} {g : T →ₕ W} {h : S+T →ₕ W}
                  → h ∘ₕ inl ≡ₕ f
                  → h ∘ₕ inr ≡ₕ g
                  → [ f , g ] ≡ₕ h
