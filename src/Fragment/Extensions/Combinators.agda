{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory
open import Fragment.Equational.FreeExtension

module Fragment.Extensions.Combinators
  (Θ : Theory)
  (Ω : FreeExtension Θ)
  where

open import Fragment.Equational.Theory.Combinators
open import Fragment.Equational.Model

open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level; _⊔_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; #_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ (A : Model (AddHom Θ) {a} {ℓ}) (n : ℕ) where

{-
AddHomFrex : FreeExtension (AddHom Θ)
AddHomFrex = record { _[_]        = {!!}
                    ; _[_]-isFrex = {!!}
                    }
-}
