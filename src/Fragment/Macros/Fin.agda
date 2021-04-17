{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Fin where

{-
open import Reflection hiding (name; Type)
open import Fragment.Macros.Base

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_; upTo; map)
open import Data.Unit using (⊤)
open import Relation.Binary using (Setoid)

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

fin-def : ℕ → Term → TC Name
fin-def n τ
  = do fin ← quoteTC (Fin n)
       let τ' = pi (vra fin) (abs "n" τ)
       η ← freshName "_"
       declareDef (vra η) τ'
       return η

fin-refl : Term → (n : ℕ) → Term → Term → TC Term
fin-refl s n f g
  = do let prop = def (quote Setoid._≈_) ( vra s
                                         ∷ vra (apply f (vra (var 0 []) ∷ []))
                                         ∷ vra (apply g (vra (var 0 []) ∷ []))
                                         ∷ [])
       fin ← quoteTC (Fin n)
       let τ = pi (hra fin) (abs "x" prop)
       η ← freshName "_"
       declareDef (vra η) τ
       defineFun η (map (λ m → fin-hclause m (def (quote Setoid.refl) (vra s ∷ []))) (upTo n))
       return (def η [])
-}
