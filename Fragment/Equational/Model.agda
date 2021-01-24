{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Model (Θ : Theory) where

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Signature

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level

open Theory Θ

{--
_⊨⟨_⟩_ : {n : ℕ}
         → (S : Setoid a ℓ)
         → (⟦_⟧ : Interpretation (Σ ⦉ n ⦊) S)
         → Eq (Σ Θ) n
         → Set a
S ⊨⟨ f ⟩ eq = ?

_⊨_ : (Algebra (Σ Θ) {a} {ℓ})
      → {n : ℕ} → Eq (Σ Θ) n
      → Set a
_⊨_ S {n} eq =
  ∀ {f : Fin n → Algebra.Carrier S} → S ⊨⟨ f ⟩ eq
--}
