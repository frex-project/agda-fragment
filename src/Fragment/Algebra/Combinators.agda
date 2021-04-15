{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.Combinators where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra

open import Level using (Level)
open import Data.Nat using (suc)
open import Data.Sum using (inj₁)

private
  variable
    a ℓ : Level

forget : ∀ {Σ n} → Algebra (Σ ⦉ n ⦊) {a} {ℓ} → Algebra Σ
forget {Σ = Σ} A = record { ∥_∥/≈           = ∥ A ∥/≈
                          ; ∥_∥/≈-isAlgebra = isAlgebra
                          }
  where forget-⟦_⟧ : Interpretation Σ ∥ A ∥/≈
        forget-⟦_⟧ {arity = 0}     f = A ⟦ inj₁ f ⟧_
        forget-⟦_⟧ {arity = suc n} f = A ⟦ f ⟧_

        forget-⟦⟧-cong : Congruence Σ ∥ A ∥/≈ forget-⟦_⟧
        forget-⟦⟧-cong {arity = 0}     f = A ⟦ inj₁ f ⟧-cong
        forget-⟦⟧-cong {arity = suc n} f = A ⟦ f ⟧-cong

        isAlgebra : IsAlgebra Σ ∥ A ∥/≈
        isAlgebra = record { ⟦_⟧     = forget-⟦_⟧
                           ; ⟦⟧-cong = forget-⟦⟧-cong
                           }
