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
open import Relation.Binary using (Setoid; Rel)

open import Algebra.Core

private
  variable
    a ℓ : Level

module _ {A : Set a} {_≈_ : Rel A ℓ} where

  open import Algebra.Definitions _≈_
  open import Algebra.Structures _≈_

  module _ {_•_ : Op₂ A} where

    module _ (isMagma : IsMagma _•_) where

      open IsMagma isMagma

      magma→setoid : Setoid a ℓ
      magma→setoid = record { Carrier       = A
                            ; _≈_           = _≈_
                            ; isEquivalence = isEquivalence
                            }

      private

        magma→⟦⟧ : Interpretation Σ-magma magma→setoid
        magma→⟦⟧ MagmaOp.• (x ∷ y ∷ []) = _•_ x y

        magma→⟦⟧-cong : Congruent₂ _•_ → Congruence Σ-magma magma→setoid magma→⟦⟧
        magma→⟦⟧-cong c MagmaOp.• (x₁≈x₂ ∷ y₁≈y₂ ∷ []) = c x₁≈x₂ y₁≈y₂

      magma→isAlgebra : IsAlgebra Σ-magma magma→setoid
      magma→isAlgebra = record { ⟦_⟧     = magma→⟦⟧
                               ; ⟦⟧-cong = magma→⟦⟧-cong ∙-cong
                               }

      magma→algebra : Algebra Σ-magma
      magma→algebra = record { ∥_∥/≈           = magma→setoid
                             ; ∥_∥/≈-isAlgebra = magma→isAlgebra
                             }

      private

        magma→models : Models Θ-magma magma→algebra
        magma→models ()

        magma→isModel : IsModel Θ-magma magma→setoid
        magma→isModel = record { isAlgebra = magma→isAlgebra
                               ; models    = magma→models
                               }

      magma→model : Model Θ-magma
      magma→model = record { ∥_∥/≈   = magma→setoid
                           ; isModel = magma→isModel
                           }

    module _ (isSemigroup : IsSemigroup _•_) where

      private

        open IsSemigroup isSemigroup renaming (assoc to •-assoc)

        semigroup→models : Models Θ-semigroup (magma→algebra isMagma)
        semigroup→models assoc θ =
          •-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

        semigroup→isModel : IsModel Θ-semigroup (magma→setoid isMagma)
        semigroup→isModel = record { isAlgebra = magma→isAlgebra isMagma
                                   ; models    = semigroup→models
                                   }

      semigroup→model : Model Θ-semigroup
      semigroup→model = record { ∥_∥/≈   = magma→setoid isMagma
                               ; isModel = semigroup→isModel
                               }
