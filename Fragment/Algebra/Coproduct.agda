{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel; IsEquivalence)
open import Algebra.Core

module Fragment.Algebra.Coproduct
  {a ℓ}
  {M : Set a} (_≈ₘ_ : Rel M ℓ)
  {N : Set a} (_≈ₙ_ : Rel N ℓ)
  where

open import Level using (_⊔_; suc)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Algebra.Structures using (IsMagma)
open import Algebra.Morphism.Definitions using (Homomorphic₂)

-------------------------------------------------------------------------------
-- Coproduct of algebras with a single binary operation
-------------------------------------------------------------------------------

record IsCoproduct₁
    {_∙ₘ_ : Op₂ M}
    {_∙ₙ_ : Op₂ N}
    (IsAlgebra : {A : Set a} → Rel A ℓ → Op₂ A → Set a)
    (_ : IsAlgebra (_≈ₘ_) (_∙ₘ_))
    (_ : IsAlgebra (_≈ₙ_) (_∙ₙ_)) : Set (suc (a ⊔ ℓ)) where
  field
    Coprod : Set a
    _≈_ : Rel Coprod ℓ
    _∙_ : Op₂ Coprod

    isAlgebra : IsAlgebra (_≈_) (_∙_)

    inl : M → Coprod
    inr : N → Coprod

    .inl-Homomorhpic₂ : Homomorphic₂ M Coprod (_≈_) inl (_∙ₘ_) (_∙_)
    .inr-Homomorhpic₂ : Homomorphic₂ N Coprod (_≈_) inr (_∙ₙ_) (_∙_)

    [_,_] : ∀ {O _≈ₒ_ _∙ₒ_ f g} {{ _ : IsAlgebra (_≈ₒ_) (_∙ₒ_) }}
            → (Homomorphic₂ M O (_≈ₒ_) f (_∙ₘ_) (_∙ₒ_))
            → (Homomorphic₂ N O (_≈ₒ_) g (_∙ₙ_) (_∙ₒ_))
            → (Coprod → O)

    .[]-Homomorhpic₂ : ∀ {O _≈ₒ_ _∙ₒ_ f g} {{ _ : IsAlgebra (_≈ₒ_) (_∙ₒ_) }}
                       → (p : Homomorphic₂ M O (_≈ₒ_) f (_∙ₘ_) (_∙ₒ_))
                       → (q : Homomorphic₂ N O (_≈ₒ_) g (_∙ₙ_) (_∙ₒ_))
                       → Homomorphic₂ Coprod O (_≈ₒ_) [ p , q ] (_∙_) (_∙ₒ_)

    -- FIXME only need to be equivalences up to _≈ₒ_ not _≡_
    .commute₁ : ∀ {O _≈ₒ_ _∙ₒ_ f g} {{ _ : IsAlgebra (_≈ₒ_) (_∙ₒ_) }}
                → (p : Homomorphic₂ M O (_≈ₒ_) f (_∙ₘ_) (_∙ₒ_))
                → (q : Homomorphic₂ N O (_≈ₒ_) g (_∙ₙ_) (_∙ₒ_))
                → [ p , q ] ∘ inl ≡ f

    .commute₂ : ∀ {O _≈ₒ_ _∙ₒ_ f g} {{ _ : IsAlgebra (_≈ₒ_) (_∙ₒ_) }}
                → (p : Homomorphic₂ M O (_≈ₒ_) f (_∙ₘ_) (_∙ₒ_))
                → (q : Homomorphic₂ N O (_≈ₒ_) g (_∙ₙ_) (_∙ₒ_))
                → [ p , q ] ∘ inr ≡ g

    .universal : ∀ {O _≈ₒ_ _∙ₒ_} {{isAlgebra : IsAlgebra (_≈ₒ_) (_∙ₒ_)}}
                 → (∀ {f g h}
                    → (p : Homomorphic₂ M O (_≈ₒ_) f (_∙ₘ_) (_∙ₒ_))
                    → (q : Homomorphic₂ N O (_≈ₒ_) g (_∙ₙ_) (_∙ₒ_))
                    → (r : Homomorphic₂ Coprod O (_≈ₒ_) h (_∙_) (_∙ₒ_))
                    → h ∘ inl ≡ f
                    → h ∘ inr ≡ g
                    → [ p , q ] ≡ h)
