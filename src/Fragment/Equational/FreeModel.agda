{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeModel (Θ : Theory) where

open import Fragment.Equational.FreeModel.Base Θ public
open import Fragment.Equational.FreeModel.Properties Θ public
