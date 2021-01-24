{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.TermAlgebra (Σ : Signature) where

open import Fragment.Algebra.TermAlgebra.Base Σ public
open import Fragment.Algebra.TermAlgebra.Properties Σ public
open import Fragment.Algebra.TermAlgebra.Syntax Σ public
