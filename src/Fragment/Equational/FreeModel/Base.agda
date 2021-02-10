{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory
open import Data.Nat using (ℕ)

module Fragment.Equational.FreeModel.Base
  (Θ : Theory)
  (n : ℕ)
  where

open import Fragment.Equational.Model
open import Fragment.Equational.TermModel (Θ ⦉ n ⦊)

|T|ₘ_⦉_⦊ : Model Θ
|T|ₘ_⦉_⦊ = record { Carrierₛ  = Herbrandₘ
                  ; isModel   = {!!}
                  }
