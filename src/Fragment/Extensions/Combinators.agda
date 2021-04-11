{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory.Base

module Fragment.Extensions.Combinators {Θ : Theory} where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Combinators
open import Fragment.Algebra.Algebra using (∥_∥/≈-isAlgebra)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Algebra
  using (Algebra; IsAlgebra; algebra; Interpretation; Congruence)

open import Fragment.Equational.Theory.Combinators
open import Fragment.Equational.Model hiding (∥_∥/≈-isAlgebra)
open import Fragment.Equational.FreeExtension
open import Fragment.Equational.Coproduct

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ)
open import Data.Fin using (zero; #_)
open import Data.Vec using ([]; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise; []; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    a ℓ : Level

module _
  (FX : FreeExtension Θ)
  (• : ops (Σ Θ) 2)
  where

  open FreeExtension FX

  forgetId : Model (AddId Θ •) {a} {ℓ} → Model Θ {a} {ℓ}
  forgetId M = record { ∥_∥/≈   = ∥ M ∥/≈
                      ; isModel = forgetId-isModel
                      }
    where forgetId-models : Models Θ (forget ∥ M ∥ₐ)
          forgetId-models eq {θ} =
            forget-⊨ {A = ∥ M ∥ₐ} {eq = Θ ⟦ eq ⟧ₑ}
              (∥ M ∥ₐ-models (inherited eq)) {θ}
          forgetId-isModel : IsModel Θ ∥ M ∥/≈
          forgetId-isModel =
            record { isAlgebra = ∥ forget ∥ M ∥ₐ ∥/≈-isAlgebra
                   ; models    = forgetId-models
                   }

  module _ (M : Model (AddId Θ •) {a} {ℓ}) (n : ℕ) where

    e : ∥ forgetId M ∥
    e = (M ⟦ inj₂ zero ⟧) []

    open IsCoproduct ((forgetId M) [ n ]-isFrex)

    open module X = Setoid ∥ (forgetId M) [ n ] ∥/≈ using (_≈_)
    open module M = Setoid ∥ M ∥/≈ renaming (_≈_ to _≈ₘ_)

    id-⟦_⟧ : Interpretation (Σ (AddId Θ •)) ∥ (forgetId M) [ n ] ∥/≈
    id-⟦ inj₁ f ⟧ []      = (((forgetId M) [ n ]) ⟦ f ⟧) []
    id-⟦ inj₂ zero ⟧ []   = ∥ inl ∥ₕ e
    id-⟦ f ⟧ (x ∷ xs)     =
      (((forgetId M) [ n ]) ⟦ f ⟧) (x ∷ xs)

    id-⟦⟧-cong : Congruence (Σ (AddId Θ •)) ∥ (forgetId M) [ n ] ∥/≈ id-⟦_⟧
    id-⟦⟧-cong (inj₁ f) []    = (((forgetId M) [ n ]) ⟦⟧-cong) f []
    id-⟦⟧-cong (inj₂ zero) [] = ∥ inl ∥ₕ-cong M.refl
    id-⟦⟧-cong f (p ∷ ps)     = (((forgetId M) [ n ]) ⟦⟧-cong) f (p ∷ ps)

    id-isAlgebra : IsAlgebra (Σ (AddId Θ •)) ∥ (forgetId M) [ n ] ∥/≈
    id-isAlgebra = record { ⟦_⟧     = id-⟦_⟧
                          ; ⟦⟧-cong = id-⟦⟧-cong
                          }

    id-algebra : Algebra (Σ (AddId Θ •))
    id-algebra = algebra ∥ (forgetId M) [ n ] ∥/≈ id-isAlgebra

    id-models : Models (AddId Θ •) id-algebra
    id-models idₗ {θ}        = {!!}
    id-models idᵣ {θ}        = {!!}
    id-models (inherited eq) = {!!}

    id-isModel : IsModel (AddId Θ •) ∥ (forgetId M) [ n ] ∥/≈
    id-isModel = record { isAlgebra = id-isAlgebra
                        ; models    = id-models
                        }

    id-model : Model (AddId Θ •) {a} {a ⊔ ℓ}
    id-model = record { ∥_∥/≈   = ∥ (forgetId M) [ n ] ∥/≈
                      ; isModel = id-isModel
                      }

  id-model-isFrex : IsFreeExtension (AddId Θ •) id-model
  id-model-isFrex M n =
    record { inl       = {!!}
           ; inr       = {!!}
           ; [_,_]     = {!!}
           ; commute₁  = {!!}
           ; commute₂  = {!!}
           ; universal = {!!}
           }
    where open IsCoproduct ((forgetId M) [ n ]-isFrex)

  AddIdFrex : FreeExtension (AddId Θ •)
  AddIdFrex = record { _[_]        = id-model
                     ; _[_]-isFrex = id-model-isFrex
                     }
