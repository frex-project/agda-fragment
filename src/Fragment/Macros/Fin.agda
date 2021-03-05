{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Fin where

open import Reflection hiding (name; Type)
open import Fragment.Macros.Base

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Vec using (toList; map; allFin)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

fin-pat : ∀ {n : ℕ} → Fin n → Pattern
fin-pat zero    = Pattern.con (quote Fin.zero) []
fin-pat (suc n) = Pattern.con (quote Fin.suc) (vra (fin-pat n) ∷ [])

fin-clause : ∀ {n : ℕ} → Fin n → Term → Clause
fin-clause n body = Clause.clause (hra (fin-pat n) ∷ []) body

macro
  fin-refl : ∀ {a} {A : Set a}
             → (n : ℕ) → (Fin n → A) → (Fin n → A)
             → Term → TC ⊤
  fin-refl {a} {A} n f g goal
    = do τ ← quoteTC (∀ {x : Fin n} → f x ≡ g x)
         η ← freshName "_"
         declareDef (vra η) τ
         defineFun η (toList (map (λ (m : Fin n) → fin-clause m (con (quote PE.refl) [])) (allFin n)))
         unify goal (def η [])
