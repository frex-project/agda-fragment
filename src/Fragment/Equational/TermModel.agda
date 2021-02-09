{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.TermModel (Θ : Theory) where

open import Fragment.Equational.TermModel.Base Θ public
open import Fragment.Equational.TermModel.Properties Θ public
