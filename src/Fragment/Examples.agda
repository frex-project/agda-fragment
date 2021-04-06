{-# OPTIONS --without-K --safe #-}

module Fragment.Examples where

open import Fragment.Prelude

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-isSemigroup)

simple : ∀ {m n} → (m + 2) + (3 + n) ≡ (m + 5) + n
simple {m} {n} = fragment SemigroupFrex
                          (semigroup→model (PE.setoid ℕ) +-isSemigroup)
                          ((m + 2) + (3 + n))
                          ((m + 5) + n)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-isSemigroup)

lists : ∀ {m n x y} → ((0 ∷ m) ++ (x ∷ [])) ++ ((y ∷ []) ++ n) ≡ (0 ∷ m) ++ (x ∷ y ∷ []) ++ n
lists {m} {n} {x} {y} = fragment SemigroupFrex
                                 (semigroup→model (PE.setoid (List ℕ)) ++-isSemigroup)
                                 (((0 ∷ m) ++ (x ∷ [])) ++ ((y ∷ []) ++ n))
                                 ((0 ∷ m) ++ (x ∷ y ∷ []) ++ n)
