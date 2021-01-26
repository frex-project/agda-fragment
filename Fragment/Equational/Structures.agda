{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Structures where

import Fragment.Equational.Laws as L
open import Fragment.Equational.Bundles
open import Fragment.Equational.Theory
open import Fragment.Equational.Model
open import Fragment.Algebra.Algebra

open import Level using (Level)
open import Data.Fin using (#_)
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary using (Setoid)

open import Algebra.Core

private
  variable
    a ℓ : Level

module _ (S : Setoid a ℓ) where

  open Setoid S renaming (Carrier to A)

  open import Algebra.Definitions _≈_
  open import Algebra.Structures _≈_

  magma→⟦⟧ : Op₂ A → Interpretation Σ-magma S
  magma→⟦⟧ f MagmaOp.• (x ∷ y ∷ []) = f x y

  magma→⟦⟧-cong : ∀ {∙} → Congruent₂ ∙
                  → Congruence Σ-magma S (magma→⟦⟧ ∙)
  magma→⟦⟧-cong cong MagmaOp.• (x₁≈x₂ ∷ y₁≈y₂ ∷ []) = cong x₁≈x₂ y₁≈y₂

  module _ {∙ : Op₂ A} (M : IsMagma ∙) where

    open IsMagma M

    magma→isAlgebra : IsAlgebra Σ-magma S
    magma→isAlgebra = record { ⟦_⟧     = magma→⟦⟧ ∙
                             ; ⟦⟧-cong = magma→⟦⟧-cong ∙-cong
                             }

    magma→algebra : Algebra Σ-magma
    magma→algebra = record { Carrierₛ  = S
                           ; isAlgebra = magma→isAlgebra
                           }

    magma→models : Models Θ-magma magma→algebra
    magma→models {_} = []

    magma→isModel : IsModel Θ-magma S
    magma→isModel = record { isAlgebra = magma→isAlgebra
                           ; models    = magma→models
                           }

    magma→model : Model Θ-magma
    magma→model = record { Carrierₛ = S
                         ; isModel  = magma→isModel
                         }

  module _ {∙ : Op₂ A} (M : IsSemigroup ∙) where

    open IsSemigroup M

    semigroup⊨assoc : (magma→algebra isMagma) ⊨ (L.assoc Σ-magma MagmaOp.•)
    semigroup⊨assoc {θ} = assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

    semigroup→models : Models Θ-semigroup (magma→algebra isMagma)
    semigroup→models {3} =
      (λ {θ} → semigroup⊨assoc {θ}) ∷ (magma→models isMagma {3})
    semigroup→models {n} = ?

    semigroup→isModel : IsModel Θ-semigroup S
    semigroup→isModel = record { isAlgebra = magma→isAlgebra isMagma
                               ; models    = semigroup→models
                               }

    semigroup→model : Model Θ-semigroup
    semigroup→model = record { Carrierₛ = S
                             ; isModel  = semigroup→isModel
                             }
