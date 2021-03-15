{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Fin where

open import Reflection hiding (name; Type)
open import Fragment.Macros.Base

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_; upTo; map)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

fin : ℕ → Term
fin zero    = con (quote Fin.zero) []
fin (suc n) = con (quote Fin.suc) (vra (fin n) ∷ [])

fin-pat : ℕ → Pattern
fin-pat zero    = Pattern.con (quote Fin.zero) []
fin-pat (suc n) = Pattern.con (quote Fin.suc) (vra (fin-pat n) ∷ [])

fin-hclause : ℕ → Term → Clause
fin-hclause n body = Clause.clause (hra (fin-pat n) ∷ []) body

fin-vclause : ℕ → Term → Clause
fin-vclause n body = Clause.clause (vra (fin-pat n) ∷ []) body

macro
  fin-refl : ∀ {a} {A : Set a}
             → (n : ℕ) → (Fin n → A) → (Fin n → A)
             → Term → TC ⊤
  fin-refl {a} {A} n f g goal
    = do τ ← quoteTC (∀ {x : Fin n} → f x ≡ g x)
         η ← freshName "_"
         declareDef (vra η) τ
         defineFun η (map (λ m → fin-hclause m (con (quote PE.refl) [])) (upTo n))
         unify goal (def η [])
