{-# OPTIONS --without-K --safe #-}

module Fragment.Equational.Structures where

import Fragment.Equational.Theory.Laws as L
open import Fragment.Equational.Theory
open import Fragment.Equational.Theory.Bundles
open import Fragment.Equational.Model

open import Fragment.Algebra.Algebra

open import Level using (Level)
open import Data.Fin using (Fin; #_; suc; zero)
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head)
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

  isAlgebra→isModel : IsAlgebra Σ-magma S → IsModel Θ-magma S
  isAlgebra→isModel isAlgebra =
    record { isAlgebra = isAlgebra
           ; models    = λ ()
           }

  module _ {∙ : Op₂ A} (M : IsMagma ∙) where

    open IsMagma M

    magma→isAlgebra : IsAlgebra Σ-magma S
    magma→isAlgebra = record { ⟦_⟧     = magma→⟦⟧ ∙
                             ; ⟦⟧-cong = magma→⟦⟧-cong ∙-cong
                             }

    magma→algebra : Algebra Σ-magma
    magma→algebra = record { ∥_∥/≈     = S
                           ; isAlgebra = magma→isAlgebra
                           }

    magma→models : Models Θ-magma magma→algebra
    magma→models ()

    magma→isModel : IsModel Θ-magma S
    magma→isModel = record { isAlgebra = magma→isAlgebra
                           ; models    = magma→models
                           }

    magma→model : Model Θ-magma
    magma→model = record { ∥_∥/≈    = S
                         ; isModel  = magma→isModel
                         }

  module _ (M : IsModel Θ-magma S) where

    open IsModel M

    isModel→∙ : Op₂ A
    isModel→∙ x y = ⟦ MagmaOp.• ⟧ (x ∷ y ∷ [])

    isModel→∙-cong : Congruent₂ isModel→∙
    isModel→∙-cong x₁≈x₂ y₁≈y₂ = ⟦⟧-cong MagmaOp.• (x₁≈x₂ ∷ y₁≈y₂ ∷ [])

    isModel→magma : IsMagma isModel→∙
    isModel→magma = record { isEquivalence = isEquivalence
                           ; ∙-cong        = isModel→∙-cong
                           }

  module _ {∙ : Op₂ A} (M : IsSemigroup ∙) where

    open IsSemigroup M

    semigroup→models : Models Θ-semigroup (magma→algebra isMagma)
    semigroup→models assoc {θ} =
      (IsSemigroup.assoc M) (θ (# 0)) (θ (# 1)) (θ (# 2))

    semigroup→isModel : IsModel Θ-semigroup S
    semigroup→isModel = record { isAlgebra = magma→isAlgebra isMagma
                               ; models    = semigroup→models
                               }

    semigroup→model : Model Θ-semigroup
    semigroup→model = record { ∥_∥/≈    = S
                             ; isModel  = semigroup→isModel
                             }

  module _ (M : IsModel Θ-semigroup S) where

    open IsModel M

    isModel→assoc : Associative (isModel→∙ (isAlgebra→isModel (isAlgebra M)))
    isModel→assoc x y z = models assoc {θ}
      where θ : Fin 3 → A
            θ zero             = x
            θ (suc zero)       = y
            θ (suc (suc zero)) = z

    isModel→semigroup : IsSemigroup (isModel→∙ (isAlgebra→isModel (isAlgebra M)))
    isModel→semigroup =
      record { isMagma = isModel→magma (isAlgebra→isModel (isAlgebra M))
             ; assoc   = isModel→assoc
             }
