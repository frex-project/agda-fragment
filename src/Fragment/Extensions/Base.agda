{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.Base where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Level using (Level)

private
  variable
    a : Level

data BT (n : ℕ) (A : Set a) : Set a where
  sta : A → BT n A
  dyn : Fin n → BT n A
