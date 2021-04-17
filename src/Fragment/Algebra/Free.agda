{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free (Σ : Signature) where

open import Fragment.Algebra.Free.Base Σ public
open import Fragment.Algebra.Free.Properties Σ public
open import Fragment.Algebra.Free.Monad Σ public
open import Fragment.Algebra.Free.Evaluation Σ public
