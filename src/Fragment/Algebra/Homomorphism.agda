{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism (Σ : Signature) where

open import Fragment.Algebra.Homomorphism.Base Σ public
open import Fragment.Algebra.Homomorphism.Definitions Σ public
open import Fragment.Algebra.Homomorphism.Properties Σ public
open import Fragment.Algebra.Homomorphism.Setoid Σ public
open import Fragment.Algebra.Homomorphism.Equivalence Σ public
