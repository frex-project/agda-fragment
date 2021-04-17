{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Model (Θ : Theory) where

open import Fragment.Equational.Model.Base Θ public
open import Fragment.Equational.Model.Synthetic Θ public
open import Fragment.Equational.Model.Properties Θ public
open import Fragment.Equational.Model.Satisfaction public
