{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Coproduct (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ

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
      inl : S ⟿ S+T
      inr : T ⟿ S+T

      [_,_] : ∀ {d ℓ₄} {W : Algebra {d} {ℓ₄}}
              → S ⟿ W → T ⟿ W → S+T ⟿ W

      commute₁ : ∀ {d ℓ₄} {W : Algebra {d} {ℓ₄}}
                 → {f : S ⟿ W} {g : T ⟿ W}
                 → [ f , g ] ⊙ inl ≗ f

      commute₂ : ∀ {d ℓ₄} {W : Algebra {d} {ℓ₄}}
                 → {f : S ⟿ W} {g : T ⟿ W}
                 → [ f , g ] ⊙ inr ≗ g

      universal : ∀ {d ℓ₄} {W : Algebra {d} {ℓ₄}}
                  → {f : S ⟿ W} {g : T ⟿ W} {h : S+T ⟿ W}
                  → h ⊙ inl ≗ f
                  → h ⊙ inr ≗ g
                  → [ f , g ] ≗ h
