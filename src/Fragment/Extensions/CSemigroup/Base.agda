{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.CSemigroup.Base where

open import Fragment.Equational.Theory.Bundles

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Free Σ-magma hiding (_~_)
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence)
open import Fragment.Equational.Model Θ-csemigroup

open import Fragment.Setoid.Morphism using (_↝_)
open import Fragment.Extensions.CSemigroup.Monomial

open import Level using (Level; _⊔_)

open import Data.Nat using (ℕ)

open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ (A : Model {a} {ℓ}) (n : ℕ) where

  private

    open module A = Setoid ∥ A ∥/≈

    _·_ : ∥ A ∥ → ∥ A ∥ → ∥ A ∥
    x · y = A ⟦ • ⟧ (x ∷ y ∷ [])

    ·-cong : ∀ {x y z w} → x ≈ y → z ≈ w → x · z ≈ y · w
    ·-cong x≈y z≈w = (A ⟦ • ⟧-cong) (x≈y ∷ z≈w ∷ [])

    ·-comm : ∀ (x y : ∥ A ∥) → x · y ≈ y · x
    ·-comm x y = ∥ A ∥ₐ-models comm (env {A = ∥ A ∥ₐ} (x ∷ y ∷ []))

    ·-assoc : ∀ (x y z : ∥ A ∥) → (x · y) · z ≈ x · (y · z)
    ·-assoc x y z = ∥ A ∥ₐ-models assoc (env {A = ∥ A ∥ₐ} (x ∷ y ∷ z ∷ []))

    data Blob : Set a where
      sta  : ∥ A ∥ → Blob
      dyn  : ∥ J' n ∥ → Blob
      blob : ∥ J' n ∥ → ∥ A ∥ → Blob

    infix 6 _≋_

    data _≋_ : Blob → Blob → Set (a ⊔ ℓ) where
      sta  : ∀ {x y} → x ≈ y → sta x ≋ sta y
      dyn  : ∀ {xs ys} → xs ≡ ys → dyn xs ≋ dyn ys
      blob : ∀ {x y xs ys} → xs ≡ ys → x ≈ y
             → blob xs x ≋ blob ys y

    ≋-refl : ∀ {x} → x ≋ x
    ≋-refl {x = sta x}     = sta A.refl
    ≋-refl {x = dyn xs}    = dyn PE.refl
    ≋-refl {x = blob xs x} = blob PE.refl A.refl

    ≋-sym : ∀ {x y} → x ≋ y → y ≋ x
    ≋-sym (sta p)     = sta (A.sym p)
    ≋-sym (dyn ps)    = dyn (PE.sym ps)
    ≋-sym (blob ps p) = blob (PE.sym ps) (A.sym p)

    ≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
    ≋-trans (sta p)     (sta q)     = sta (A.trans p q)
    ≋-trans (dyn ps)    (dyn qs)    = dyn (PE.trans ps qs)
    ≋-trans (blob ps p) (blob qs q) = blob (PE.trans ps qs) (A.trans p q)

    ≋-isEquivalence : IsEquivalence _≋_
    ≋-isEquivalence = record { refl  = ≋-refl
                             ; sym   = ≋-sym
                             ; trans = ≋-trans
                             }

    Blob/≋ : Setoid _ _
    Blob/≋ = record { Carrier       = Blob
                    ; _≈_           = _≋_
                    ; isEquivalence = ≋-isEquivalence
                    }

    _++_ : Blob → Blob → Blob
    sta x     ++ sta y     = sta (x · y)
    dyn xs    ++ dyn ys    = dyn (xs ⊗ ys)
    sta x     ++ dyn ys    = blob ys        x
    sta x     ++ blob ys y = blob ys        (x · y)
    dyn xs    ++ sta y     = blob xs        y
    dyn xs    ++ blob ys y = blob (xs ⊗ ys) y
    blob xs x ++ sta y     = blob xs        (x · y)
    blob xs x ++ dyn ys    = blob (xs ⊗ ys) x
    blob xs x ++ blob ys y = blob (xs ⊗ ys) (x · y)

    ++-cong : ∀ {x y z w} → x ≋ y → z ≋ w → x ++ z ≋ y ++ w
    ++-cong (sta p)     (sta q)     = sta (·-cong p q)
    ++-cong (dyn ps)    (dyn qs)    = dyn (⊗-cong ps qs)
    ++-cong (sta p)     (dyn qs)    = blob qs p
    ++-cong (sta p)     (blob qs q) = blob qs (·-cong p q)
    ++-cong (dyn ps)    (sta q)     = blob ps q
    ++-cong (dyn ps)    (blob qs q) = blob (⊗-cong ps qs) q
    ++-cong (blob ps p) (sta q)     = blob ps (·-cong p q)
    ++-cong (blob ps p) (dyn qs)    = blob (⊗-cong ps qs) p
    ++-cong (blob ps p) (blob qs q) = blob (⊗-cong ps qs) (·-cong p q)

    ++-comm : ∀ x y → x ++ y ≋ y ++ x
    ++-comm (sta x)     (sta y)     = sta (·-comm x y)
    ++-comm (dyn xs)    (dyn ys)    = dyn (⊗-comm xs ys)
    ++-comm (sta x)     (dyn ys)    = ≋-refl
    ++-comm (sta x)     (blob ys y) = blob PE.refl (·-comm x y)
    ++-comm (dyn xs)    (sta y)     = ≋-refl
    ++-comm (dyn xs)    (blob ys y) = blob (⊗-comm xs ys) A.refl
    ++-comm (blob xs x) (sta y)     = blob PE.refl (·-comm x y)
    ++-comm (blob xs x) (dyn ys)    = blob (⊗-comm xs ys) A.refl
    ++-comm (blob xs x) (blob ys y) = blob (⊗-comm xs ys) (·-comm x y)

    ++-assoc : ∀ x y z → (x ++ y) ++ z ≋ x ++ (y ++ z)
    ++-assoc (sta x)     (sta y)     (sta z)     = sta (·-assoc x y z)
    ++-assoc (dyn xs)    (dyn ys)    (dyn zs)    = dyn (⊗-assoc xs ys zs)
    ++-assoc (sta x)     (sta y)     (dyn zs)    = ≋-refl
    ++-assoc (sta x)     (sta y)     (blob zs z) = blob PE.refl (·-assoc x y z)
    ++-assoc (sta x)     (dyn ys)    (sta z)     = ≋-refl
    ++-assoc (sta x)     (dyn ys)    (dyn zs)    = ≋-refl
    ++-assoc (sta x)     (dyn ys)    (blob zs z) = ≋-refl
    ++-assoc (sta x)     (blob ys y) (sta z)     = blob PE.refl (·-assoc x y z)
    ++-assoc (sta x)     (blob ys y) (dyn zs)    = ≋-refl
    ++-assoc (sta x)     (blob ys y) (blob zs z) = blob PE.refl (·-assoc x y z)
    ++-assoc (dyn xs)    (sta y)     (sta z)     = ≋-refl
    ++-assoc (dyn xs)    (sta y)     (dyn zs)    = ≋-refl
    ++-assoc (dyn xs)    (sta y)     (blob zs z) = ≋-refl
    ++-assoc (dyn xs)    (dyn ys)    (sta z)     = ≋-refl
    ++-assoc (dyn xs)    (dyn ys)    (blob zs z) = blob (⊗-assoc xs ys zs) A.refl
    ++-assoc (dyn xs)    (blob ys y) (sta z)     = ≋-refl
    ++-assoc (dyn xs)    (blob ys y) (dyn zs)    = blob (⊗-assoc xs ys zs) A.refl
    ++-assoc (dyn xs)    (blob ys y) (blob zs z) = blob (⊗-assoc xs ys zs) A.refl
    ++-assoc (blob xs x) (sta y)     (sta z)     = blob PE.refl (·-assoc x y z)
    ++-assoc (blob xs x) (sta y)     (dyn zs)    = ≋-refl
    ++-assoc (blob xs x) (sta y)     (blob zs z) = blob PE.refl (·-assoc x y z)
    ++-assoc (blob xs x) (dyn ys)    (sta z)     = ≋-refl
    ++-assoc (blob xs x) (dyn ys)    (dyn zs)    = blob (⊗-assoc xs ys zs) A.refl
    ++-assoc (blob xs x) (dyn ys)    (blob zs z) = blob (⊗-assoc xs ys zs) A.refl
    ++-assoc (blob xs x) (blob ys y) (sta z)     = blob PE.refl (·-assoc x y z)
    ++-assoc (blob xs x) (blob ys y) (dyn zs)    = blob (⊗-assoc xs ys zs) A.refl
    ++-assoc (blob xs x) (blob ys y) (blob zs z) = blob (⊗-assoc xs ys zs) (·-assoc x y z)
