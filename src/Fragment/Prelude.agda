{-# OPTIONS --without-K --safe #-}

module Fragment.Prelude where

open import Fragment.Macros.Fragment public
open import Fragment.Equational.Structures public

open import Fragment.Extensions.Semigroup
  using () renaming (++-isFrex to SemigroupFrex) public
