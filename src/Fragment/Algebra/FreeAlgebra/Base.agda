{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature
open import Data.Nat using (ℕ)

module Fragment.Algebra.FreeAlgebra.Base
  (Σ : Signature)
  (n : ℕ)
  where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.TermAlgebra (Σ ⦉ n ⦊)

import Relation.Binary.PropositionalEquality as PE
open import Level using (Level)
open import Data.Sum using (inj₁)
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)

|T|_⦉_⦊-⟦_⟧ : Interpretation Σ Herbrand
|T|_⦉_⦊-⟦_⟧ f []       = term (inj₁ f) []
|T|_⦉_⦊-⟦_⟧ f (x ∷ xs) = term f (x ∷ xs)

|T|_⦉_⦊-⟦⟧-cong : Congruence Σ Herbrand |T|_⦉_⦊-⟦_⟧
|T|_⦉_⦊-⟦⟧-cong f p = PE.cong (|T|_⦉_⦊-⟦_⟧ f) (≋⇒≡ p)

|T|_⦉_⦊-isAlgebra : IsAlgebra Σ Herbrand
|T|_⦉_⦊-isAlgebra = record { ⟦_⟧     = |T|_⦉_⦊-⟦_⟧
                           ; ⟦⟧-cong = |T|_⦉_⦊-⟦⟧-cong
                           }

|T|_⦉_⦊ : Algebra Σ
|T|_⦉_⦊ = record { Carrierₛ  = Herbrand
                 ; isAlgebra = |T|_⦉_⦊-isAlgebra
                 }
