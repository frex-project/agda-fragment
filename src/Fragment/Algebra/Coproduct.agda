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
  (A : Algebra {a} {ℓ₁})
  (B : Algebra {b} {ℓ₂})
  (A+B : Algebra {c} {ℓ₃})
  where

  record IsCoproduct : Setω where
    field
      inl : A ⟿ A+B
      inr : B ⟿ A+B

      _[_,_] : ∀ {d ℓ₄} (X : Algebra {d} {ℓ₄})
               → A ⟿ X → B ⟿ X → A+B ⟿ X

      commute₁ : ∀ {d ℓ₄} {X : Algebra {d} {ℓ₄}}
                 → {f : A ⟿ X} {g : B ⟿ X}
                 → X [ f , g ] ⊙ inl ≗ f

      commute₂ : ∀ {d ℓ₄} {X : Algebra {d} {ℓ₄}}
                 → {f : A ⟿ X} {g : B ⟿ X}
                 → X [ f , g ] ⊙ inr ≗ g

      universal : ∀ {d ℓ₄} {X : Algebra {d} {ℓ₄}}
                  → {f : A ⟿ X} {g : B ⟿ X} {h : A+B ⟿ X}
                  → h ⊙ inl ≗ f
                  → h ⊙ inr ≗ g
                  → X [ f , g ] ≗ h
