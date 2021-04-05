{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Structures using (IsDecEquivalence)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (yes; no)

module Fragment.Macros.Environment
  {a ℓ}
  (A : Set a)
  (_≈_ : Rel A ℓ)
  {{isDecEquivalence : IsDecEquivalence _≈_}}
  where

open IsDecEquivalence isDecEquivalence

open import Level using (_⊔_)
open import Function using (_∘_)

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)

Environment : ∀ {b} (B : Set b) → Set (a ⊔ b)
Environment B = List (A × B)

empty : ∀ {b} {B : Set b} → Environment B
empty = []

listKeys : ∀ {b} {B : Set b} → Environment B → List A
listKeys e = foldr (_∷_ ∘ proj₁) [] e

keys : ∀ {b} {B : Set b} → Environment B → ℕ
keys e = foldr (λ _ → suc) 0 e

lookup : ∀ {b} {B : Set b} → A → Environment B → Maybe B
lookup k₁ [] = nothing
lookup k₁ ((k₂ , v) ∷ xs)
  with k₁ ≟ k₂
... | yes _ = just v
... | _     = lookup k₁ xs

set : ∀ {b} {B : Set b} → A → B → Environment B → Environment B
set k₁ v₁ [] = (k₁ , v₁) ∷ []
set k₁ v₁ ((k₂ , v₂) ∷ xs)
  with k₁ ≟ k₂
... | yes _ = (k₁ , v₁) ∷ xs
... | _     = (k₂ , v₂) ∷ set k₁ v₁ xs

lookupDefault : ∀ {b} {B : Set b} → A → Environment B → B → (B × Environment B)
lookupDefault k e v with lookup k e
...                    | just v' = (v' , e)
...                    | nothing = (v , set k v e)

setDefault : ∀ {b} {B : Set b} → A → Environment B → B → Environment B
setDefault k e v = proj₂ (lookupDefault k e v)
