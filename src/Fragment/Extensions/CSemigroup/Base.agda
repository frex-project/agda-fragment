{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.CSemigroup.Base where

open import Fragment.Equational.Theory.Bundles

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Free Σ-magma hiding (_~_)
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence)

open import Fragment.Equational.FreeExtension Θ-csemigroup
  using (FreeExtension; IsFreeExtension)
open import Fragment.Equational.Model Θ-csemigroup
open import Fragment.Extensions.CSemigroup.Monomial

open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level; _⊔_)

open import Data.Nat using (ℕ)
open import Data.Fin using (#_)

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

  Blob⟦_⟧ : Interpretation Blob/≋
  Blob⟦ • ⟧ (x ∷ y ∷ []) = x ++ y

  Blob⟦_⟧-cong : Congruence Blob/≋ Blob⟦_⟧
  Blob⟦ • ⟧-cong (p ∷ q ∷ []) = ++-cong p q

  Blob/≋-isAlgebra : IsAlgebra Blob/≋
  Blob/≋-isAlgebra = record { ⟦_⟧     = Blob⟦_⟧
                            ; ⟦⟧-cong = Blob⟦_⟧-cong
                            }

  Blob/≋-algebra : Algebra
  Blob/≋-algebra =
    record { ∥_∥/≈           = Blob/≋
           ; ∥_∥/≈-isAlgebra = Blob/≋-isAlgebra
           }

  Blob/≋-models : Models Blob/≋-algebra
  Blob/≋-models comm θ  = ++-comm (θ (# 0)) (θ (# 1))
  Blob/≋-models assoc θ = ++-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

  Blob/≋-isModel : IsModel Blob/≋
  Blob/≋-isModel =
    record { isAlgebra = Blob/≋-isAlgebra
           ; models    = Blob/≋-models
           }

  Frex : Model
  Frex = record { ∥_∥/≈   = Blob/≋
                ; isModel = Blob/≋-isModel
                }

  ∣inl∣ : ∥ A ∥ → ∥ Frex ∥
  ∣inl∣ = sta

  ∣inl∣-cong : Congruent _≈_ _≋_ ∣inl∣
  ∣inl∣-cong = sta

  ∣inl∣⃗ : ∥ A ∥/≈ ↝ ∥ Frex ∥/≈
  ∣inl∣⃗ = record { ∣_∣      = ∣inl∣
                  ; ∣_∣-cong = ∣inl∣-cong
                  }

  ∣inl∣-hom : Homomorphic ∥ A ∥ₐ ∥ Frex ∥ₐ ∣inl∣
  ∣inl∣-hom • (x ∷ y ∷ []) = ≋-refl

  inl : ∥ A ∥ₐ ⟿ ∥ Frex ∥ₐ
  inl = record { ∣_∣⃗    = ∣inl∣⃗
               ; ∣_∣-hom = ∣inl∣-hom
               }

  ∣inr∣ : ∥ J n ∥ → ∥ Frex ∥
  ∣inr∣ x = dyn (∣ norm ∣ x)

  ∣inr∣-cong : Congruent ≈[ J n ] _≋_ ∣inr∣
  ∣inr∣-cong p = dyn (∣ norm ∣-cong p)

  ∣inr∣⃗ : ∥ J n ∥/≈ ↝ ∥ Frex ∥/≈
  ∣inr∣⃗ = record { ∣_∣      = ∣inr∣
                  ; ∣_∣-cong = ∣inr∣-cong
                  }

  ∣inr∣-hom : Homomorphic ∥ J n ∥ₐ ∥ Frex ∥ₐ ∣inr∣
  ∣inr∣-hom • (x ∷ y ∷ []) = dyn (∣ norm ∣-hom • (x ∷ y ∷ []))


  inr : ∥ J n ∥ₐ ⟿ ∥ Frex ∥ₐ
  inr = record { ∣_∣⃗    = ∣inr∣⃗
               ; ∣_∣-hom = ∣inr∣-hom
               }

  module _ {b ℓ} (X : Model {b} {ℓ}) where

    private

      open module X = Setoid ∥ X ∥/≈ renaming (_≈_ to _~_)

      _⊕_ : ∥ X ∥ → ∥ X ∥ → ∥ X ∥
      x ⊕ y = X ⟦ • ⟧ (x ∷ y ∷ [])

      ⊕-cong : ∀ {x y z w} → x ~ y → z ~ w → x ⊕ z ~ y ⊕ w
      ⊕-cong p q = (X ⟦ • ⟧-cong) (p ∷ q ∷ [])

      ⊕-comm : ∀ (x y : ∥ X ∥) → x ⊕ y ~ y ⊕ x
      ⊕-comm x y = ∥ X ∥ₐ-models comm (env {A = ∥ X ∥ₐ} (x ∷ y ∷ []))

      ⊕-assoc : ∀ (x y z : ∥ X ∥) → (x ⊕ y) ⊕ z ~ x ⊕ (y ⊕ z)
      ⊕-assoc x y z = ∥ X ∥ₐ-models assoc (env {A = ∥ X ∥ₐ} (x ∷ y ∷ z ∷ []))

    module _
      (f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ)
      (g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ)
      where

      ∣resid∣ : ∥ Frex ∥ → ∥ X ∥
      ∣resid∣ (sta x)     = ∣ f ∣ x
      ∣resid∣ (dyn xs)    = ∣ g ∣ (∣ syn ∣ xs)
      ∣resid∣ (blob xs x) = ∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ f ∣ x

      ∣resid∣-cong : Congruent _≋_ _~_ ∣resid∣
      ∣resid∣-cong (sta p)     = ∣ f ∣-cong p
      ∣resid∣-cong (dyn ps)    = ∣ g ∣-cong (∣ syn ∣-cong ps)
      ∣resid∣-cong (blob ps p) =
        ⊕-cong (∣ g ∣-cong (∣ syn ∣-cong ps)) (∣ f ∣-cong p)

      open Reasoning ∥ X ∥/≈

      ∣resid∣-hom : Homomorphic ∥ Frex ∥ₐ ∥ X ∥ₐ ∣resid∣
      ∣resid∣-hom • (sta x     ∷ sta y     ∷ []) = ∣ f ∣-hom • (x ∷ y ∷ [])
      ∣resid∣-hom • (sta x     ∷ dyn ys    ∷ []) = ⊕-comm (∣ f ∣ x) _
      ∣resid∣-hom • (sta x     ∷ blob ys y ∷ []) = begin
          ∣ f ∣ x ⊕ (∣ g ∣ (∣ syn ∣ ys) ⊕ ∣ f ∣ y)
        ≈⟨ ⊕-cong X.refl (⊕-comm _ (∣ f ∣ y)) ⟩
          ∣ f ∣ x ⊕ (∣ f ∣ y ⊕ ∣ g ∣ (∣ syn ∣ ys))
        ≈⟨ X.sym (⊕-assoc (∣ f ∣ x) (∣ f ∣ y) _) ⟩
          (∣ f ∣ x ⊕ ∣ f ∣ y) ⊕ ∣ g ∣ (∣ syn ∣ ys)
        ≈⟨ ⊕-cong (∣ f ∣-hom • (x ∷ y ∷ [])) X.refl ⟩
          ∣ f ∣ (x · y) ⊕ ∣ g ∣ (∣ syn ∣ ys)
        ≈⟨ ⊕-comm _ _ ⟩
          ∣ g ∣ (∣ syn ∣ ys) ⊕ ∣ f ∣ (x · y)
        ∎
      ∣resid∣-hom • (dyn xs    ∷ sta y     ∷ []) = X.refl
      ∣resid∣-hom • (dyn xs    ∷ dyn ys    ∷ []) = ∣ g ⊙ syn ∣-hom • (xs ∷ ys ∷ [])
      ∣resid∣-hom • (dyn xs    ∷ blob ys y ∷ []) = begin
          ∣ g ∣ (∣ syn ∣ xs) ⊕ (∣ g ∣ (∣ syn ∣ ys) ⊕ ∣ f ∣ y)
        ≈⟨ X.sym (⊕-assoc _ _ (∣ f ∣ y)) ⟩
          (∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ g ∣ (∣ syn ∣ ys)) ⊕ ∣ f ∣ y
        ≈⟨ ⊕-cong (∣ g ⊙ syn ∣-hom • (xs ∷ ys ∷ [])) X.refl ⟩
          ∣ g ∣ (∣ syn ∣ (xs ⊗ ys)) ⊕ ∣ f ∣ y
        ∎
      ∣resid∣-hom • (blob xs x ∷ sta y     ∷ []) = begin
          (∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ f ∣ x) ⊕ ∣ f ∣ y
        ≈⟨ ⊕-assoc _ (∣ f ∣ x) (∣ f ∣ y) ⟩
          ∣ g ∣ (∣ syn ∣ xs) ⊕ (∣ f ∣ x ⊕ ∣ f ∣ y)
        ≈⟨ ⊕-cong X.refl (∣ f ∣-hom • (x ∷ y ∷ [])) ⟩
          ∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ f ∣ (x · y)
        ∎
      ∣resid∣-hom • (blob xs x ∷ dyn ys    ∷ []) = begin
          (∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ f ∣ x) ⊕ ∣ g ∣ (∣ syn ∣ ys)
        ≈⟨ ⊕-assoc _ (∣ f ∣ x) _ ⟩
          ∣ g ∣ (∣ syn ∣ xs) ⊕ (∣ f ∣ x ⊕ ∣ g ∣ (∣ syn ∣ ys))
        ≈⟨ ⊕-cong X.refl (⊕-comm (∣ f ∣ x) _) ⟩
          ∣ g ∣ (∣ syn ∣ xs) ⊕ (∣ g ∣ (∣ syn ∣ ys) ⊕ ∣ f ∣ x)
        ≈⟨ X.sym (⊕-assoc _ _ (∣ f ∣ x)) ⟩
          (∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ g ∣ (∣ syn ∣ ys)) ⊕ ∣ f ∣ x
        ≈⟨ ⊕-cong (∣ g ⊙ syn ∣-hom • (xs ∷ ys ∷ [])) X.refl ⟩
          ∣ g ∣ (∣ syn ∣ (xs ⊗ ys)) ⊕ ∣ f ∣ x
        ∎
      ∣resid∣-hom • (blob xs x ∷ blob ys y ∷ []) = begin
          (∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ f ∣ x) ⊕ (∣ g ∣ (∣ syn ∣ ys) ⊕ ∣ f ∣ y)
        ≈⟨ ⊕-assoc _ (∣ f ∣ x) _ ⟩
          ∣ g ∣ (∣ syn ∣ xs) ⊕ (∣ f ∣ x ⊕ (∣ g ∣ (∣ syn ∣ ys) ⊕ ∣ f ∣ y))
        ≈⟨ ⊕-cong X.refl (X.sym (⊕-assoc (∣ f ∣ x) _ _)) ⟩
          ∣ g ∣ (∣ syn ∣ xs) ⊕ ((∣ f ∣ x ⊕ ∣ g ∣ (∣ syn ∣ ys)) ⊕ ∣ f ∣ y)
        ≈⟨ ⊕-cong X.refl (⊕-cong (⊕-comm (∣ f ∣ x) _) X.refl) ⟩
          ∣ g ∣ (∣ syn ∣ xs) ⊕ ((∣ g ∣ (∣ syn ∣ ys) ⊕ ∣ f ∣ x) ⊕ ∣ f ∣ y)
        ≈⟨ ⊕-cong X.refl (⊕-assoc _ (∣ f ∣ x) _) ⟩
          ∣ g ∣ (∣ syn ∣ xs) ⊕ (∣ g ∣ (∣ syn ∣ ys) ⊕ (∣ f ∣ x ⊕ ∣ f ∣ y))
        ≈⟨ X.sym (⊕-assoc _ _ _) ⟩
          (∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ g ∣ (∣ syn ∣ ys)) ⊕ (∣ f ∣ x ⊕ ∣ f ∣ y)
        ≈⟨ ⊕-cong (∣ g ⊙ syn ∣-hom • (xs ∷ ys ∷ [])) (∣ f ∣-hom • (x ∷ y ∷ [])) ⟩
          ∣ g ∣ (∣ syn ∣ (xs ⊗ ys)) ⊕ ∣ f ∣ (x · y)
        ∎

      ∣resid∣⃗ : ∥ Frex ∥/≈ ↝ ∥ X ∥/≈
      ∣resid∣⃗ = record { ∣_∣      = ∣resid∣
                        ; ∣_∣-cong = ∣resid∣-cong
                        }

      _[_,_] : ∥ Frex ∥ₐ ⟿ ∥ X ∥ₐ
      _[_,_] = record { ∣_∣⃗    = ∣resid∣⃗
                      ; ∣_∣-hom = ∣resid∣-hom
                      }

  module _ {b ℓ} {X : Model {b} {ℓ}} where

    private

      open module X = Setoid ∥ X ∥/≈ renaming (_≈_ to _~_)

      _⊕_ : ∥ X ∥ → ∥ X ∥ → ∥ X ∥
      x ⊕ y = X ⟦ • ⟧ (x ∷ y ∷ [])

      ⊕-cong : ∀ {x y z w} → x ~ y → z ~ w → x ⊕ z ~ y ⊕ w
      ⊕-cong p q = (X ⟦ • ⟧-cong) (p ∷ q ∷ [])

      ⊕-comm : ∀ (x y : ∥ X ∥) → x ⊕ y ~ y ⊕ x
      ⊕-comm x y = ∥ X ∥ₐ-models comm (env {A = ∥ X ∥ₐ} (x ∷ y ∷ []))

      ⊕-assoc : ∀ (x y z : ∥ X ∥) → (x ⊕ y) ⊕ z ~ x ⊕ (y ⊕ z)
      ⊕-assoc x y z = ∥ X ∥ₐ-models assoc (env {A = ∥ X ∥ₐ} (x ∷ y ∷ z ∷ []))

    module _
      {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
      {g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ}
      where

      commute₁ : X [ f , g ] ⊙ inl ≗ f
      commute₁ = X.refl

      commute₂ : X [ f , g ] ⊙ inr ≗ g
      commute₂ {x} = ∣ g ∣-cong (syn⊙norm≗id {x = x})

      module _ {h : ∥ Frex ∥ₐ ⟿ ∥ X ∥ₐ}
        (c₁ : h ⊙ inl ≗ f)
        (c₂ : h ⊙ inr ≗ g)
        where

        open Reasoning ∥ X ∥/≈

        universal : X [ f , g ] ≗ h
        universal {sta x}     = X.sym c₁
        universal {dyn xs}    = begin
            ∣ g ∣ (∣ syn ∣ xs)
          ≈⟨ X.sym c₂ ⟩
            ∣ h ∣ (dyn (∣ norm ∣ (∣ syn ∣ xs)))
          ≈⟨ ∣ h ∣-cong (dyn norm⊙syn≗id) ⟩
            ∣ h ∣ (dyn xs)
          ∎
        universal {blob xs x} = begin
            ∣ g ∣ (∣ syn ∣ xs) ⊕ ∣ f ∣ x
          ≈⟨ ⊕-cong universal universal ⟩
            ∣ h ∣ (dyn xs) ⊕ ∣ h ∣ (sta x)
          ≈⟨ ∣ h ∣-hom • (dyn xs ∷ sta x ∷ []) ⟩
            ∣ h ∣ (blob xs x)
          ∎

CSemigroupFrex : FreeExtension
CSemigroupFrex = record { _[_]        = Frex
                        ; _[_]-isFrex = isFrex
                        }
  where isFrex : IsFreeExtension Frex
        isFrex A n =
          record { inl       = inl A n
                 ; inr       = inr A n
                 ; _[_,_]    = _[_,_] A n
                 ; commute₁  = λ {_ _ X f g} → commute₁ A n {X = X} {f} {g}
                 ; commute₂  = λ {_ _ X f g} → commute₂ A n {X = X} {f} {g}
                 ; universal = λ {_ _ X f g h} → universal A n {X = X} {f} {g} {h}
                 }
