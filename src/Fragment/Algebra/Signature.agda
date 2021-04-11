{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.Signature where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to Fin-dec)
open import Data.Sum using (_⊎_)
open import Data.Sum.Properties using (≡-dec)

open import Relation.Nullary using (yes ; no)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

record Signature : Set₁ where
  field
    ops : ℕ → Set
    _≟_ : ∀ {n} → Decidable {A = ops n} _≡_

open Signature using (ops) public

_⦉_⦊ : (Σ : Signature) → ℕ → Signature
Σ ⦉ n ⦊ = record { ops = extend n
                 ; _≟_ = λ {k} → _≟_ {k}
                 }
  where open Signature Σ using () renaming (_≟_ to _≈_)
        extend : ℕ → ℕ → Set
        extend n 0 = (ops Σ 0) ⊎ Fin n
        extend _ k = ops Σ k
        _≟_ : ∀ {k} → Decidable {A = extend n k} _≡_
        _≟_ {k = 0} = ≡-dec _≈_ Fin-dec
        _≟_ {k = suc k} = _≈_
