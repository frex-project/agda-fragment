{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra.Core

module Fragment.Algebra.Coproduct
  {a ℓ}
  {M : Set a} (_≈ₘ_ : Rel M ℓ)
  {N : Set a} (_≈ₙ_ : Rel N ℓ)
  where

open import Level using (_⊔_; Setω)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Algebra.Structures using (IsMagma)

-------------------------------------------------------------------------------
-- Coproduct of algebras with a single binary operation
-------------------------------------------------------------------------------

record IsCoproduct₁
    {_∙ₘ_ : Op₂ M}
    {_∙ₙ_ : Op₂ N}
    (_ : IsMagma (_≈ₘ_) (_∙ₘ_))
    (_ : IsMagma (_≈ₙ_) (_∙ₙ_)) : Setω where
  field
    Coprod : Set a
    _≈_ : Rel Coprod ℓ
    _∙_ : Op₂ Coprod

    isMagma : IsMagma (_≈_) (_∙_)

    inl : M → Coprod
    inr : N → Coprod

    [_,_] : ∀ {O : Set a} {_≈ₒ_ : Rel O ℓ} {_∙ₒ_ : Op₂ O}
              {{ _ : IsMagma (_≈ₒ_) (_∙ₒ_) }}
            → (M → O) → (N → O) → (Coprod → O)

    .commute₁ : ∀ {O : Set a} {_≈ₒ_ : Rel O ℓ} {_∙ₒ_ : Op₂ O}
                  {{isMagma : IsMagma (_≈ₒ_) (_∙ₒ_)}}
                → (f : M → O)
                → (g : N → O)
                → [ f , g ] ∘ inl ≡ f

    .commute₂ : ∀ {O : Set a} {_≈ₒ_ : Rel O ℓ} {_∙ₒ_ : Op₂ O}
                  {{isMagma : IsMagma (_≈ₒ_) (_∙ₒ_)}}
                → (f : M → O)
                → (g : N → O)
                → [ f , g ] ∘ inr ≡ g

    .universal : ∀ {O : Set a} {_≈ₒ_ : Rel O ℓ} (_∙ₒ_ : Op₂ O)
                   {{isMagma : IsMagma (_≈ₒ_) (_∙ₒ_)}}
                 → (∀ {f : M → O} {g : N → O} {h : Coprod → O}
                    → h ∘ inl ≡ f
                    → h ∘ inr ≡ g
                    → [ f , g ] ≡ h)
