{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Properties where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Free

open import Level using (Level)

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)

private
  variable
    a ℓ : Level

mutual
  map-extend : ∀ {Σ O a n} → {A : Set a}
               → Vec (Term Σ A) n
               → Vec (Term (Σ ⦅ O ⦆) A) n
  map-extend []       = []
  map-extend (x ∷ xs) = extend x ∷ map-extend xs

  extend : ∀ {Σ O} → {A : Set a}
           → Term Σ A → Term (Σ ⦅ O ⦆) A
  extend (atom x)    = atom x
  extend (term f xs) = term (old f) (map-extend xs)

forget : ∀ {Σ O} → Algebra (Σ ⦅ O ⦆) {a} {ℓ} → Algebra Σ {a} {ℓ}
forget {Σ = Σ} A = record { ∥_∥/≈           = ∥ A ∥/≈
                          ; ∥_∥/≈-isAlgebra = forget-isAlgebra
                          }
  where forget-⟦_⟧ : Interpretation Σ ∥ A ∥/≈
        forget-⟦ f ⟧ x = A ⟦ old f ⟧ x

        forget-⟦⟧-cong : Congruence Σ ∥ A ∥/≈ forget-⟦_⟧
        forget-⟦⟧-cong f x = (A ⟦ old f ⟧-cong) x

        forget-isAlgebra : IsAlgebra Σ ∥ A ∥/≈
        forget-isAlgebra = record { ⟦_⟧     = forget-⟦_⟧
                                  ; ⟦⟧-cong = forget-⟦⟧-cong
                                  }
