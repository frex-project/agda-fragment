{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature
open import Data.Nat using (ℕ)

module Fragment.Algebra.FreeAlgebra.Base
  (Σ : Signature)
  (n : ℕ)
  where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.TermAlgebra (Σ ⦉ n ⦊)

open import Level using (Level)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)
import Relation.Binary.PropositionalEquality as PE

pattern term₁ x = term (inj₁ x) []
pattern term₂ x = term (inj₂ x) []

|T|⦉_⦊-⟦_⟧ : Interpretation Herbrand
|T|⦉_⦊-⟦_⟧ f []       = term₁ f
|T|⦉_⦊-⟦_⟧ f (x ∷ xs) = term f (x ∷ xs)

|T|⦉_⦊-⟦⟧-cong : Congruence Herbrand |T|⦉_⦊-⟦_⟧
|T|⦉_⦊-⟦⟧-cong f p = PE.cong (|T|⦉_⦊-⟦_⟧ f) (≋⇒≡ p)

|T|⦉_⦊-isAlgebra : IsAlgebra Herbrand
|T|⦉_⦊-isAlgebra = record { ⟦_⟧     = |T|⦉_⦊-⟦_⟧
                           ; ⟦⟧-cong = |T|⦉_⦊-⟦⟧-cong
                           }

|T|⦉_⦊ : Algebra
|T|⦉_⦊ = record { ∥_∥/≈     = Herbrand
                ; isAlgebra = |T|⦉_⦊-isAlgebra
                }
