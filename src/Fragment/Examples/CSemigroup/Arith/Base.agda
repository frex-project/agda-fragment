{-# OPTIONS --without-K --safe #-}

module Fragment.Examples.CSemigroup.Arith.Base where

open import Fragment.Examples.Semigroup.Arith.Base public
open import Data.Nat.Properties
  using (*-isCommutativeSemigroup; +-isCommutativeSemigroup)

+-csemigroup = csemigroup→model +-isCommutativeSemigroup
*-csemigroup = csemigroup→model *-isCommutativeSemigroup
