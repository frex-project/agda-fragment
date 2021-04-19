{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension (Θ : Theory) where

open import Fragment.Equational.FreeExtension.Base Θ public
open import Fragment.Equational.FreeExtension.Synthetic Θ using (SynFrex) public
open import Fragment.Equational.FreeExtension.Properties Θ public
