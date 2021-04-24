{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.Semigroup where

open import Fragment.Equational.Theory.Bundles

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Free Σ-magma hiding (_~_)
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence; algebra)

open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.Model Θ-semigroup

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

module _ (A : Model {a} {ℓ}) (n : ℕ) where

  private

    open module A = Setoid ∥ A ∥/≈

    _·_ : ∥ A ∥ → ∥ A ∥ → ∥ A ∥
    x · y = A ⟦ • ⟧ (x ∷ y ∷ [])

    ·-cong : ∀ {x y z w} → x ≈ y → z ≈ w → x · z ≈ y · w
    ·-cong x≈y z≈w = (A ⟦ • ⟧-cong) (x≈y ∷ z≈w ∷ [])

    ·-assoc : ∀ (x y z : ∥ A ∥) → (x · y) · z ≈ x · (y · z)
    ·-assoc x y z = ∥ A ∥ₐ-models assoc (env {A = ∥ A ∥ₐ} (x ∷ y ∷ z ∷ []))

    mutual

      data STree : Set a where
        leaf : ∥ A ∥ → STree
        cons : ∥ A ∥ → DTree → STree

      data DTree : Set a where
        leaf : Fin n → DTree
        cons : Fin n → Tree → DTree

      data Tree : Set a where
        sta : STree → Tree
        dyn : DTree → Tree

    mutual

      infix 6 _≋_ _≋⟨s⟩_ _≋⟨d⟩_

      data _≋⟨s⟩_ : STree → STree → Set (a ⊔ ℓ) where
        leaf : ∀ {x y} → x ≈ y → leaf x ≋⟨s⟩ leaf y
        cons : ∀ {x y xs ys} → x ≈ y → xs ≋⟨d⟩ ys
               → cons x xs ≋⟨s⟩ cons y ys

      data _≋⟨d⟩_ : DTree → DTree → Set (a ⊔ ℓ) where
        leaf : ∀ {x y} → x ≡ y → leaf x ≋⟨d⟩ leaf y
        cons : ∀ {x y xs ys} → x ≡ y → xs ≋ ys
               → cons x xs ≋⟨d⟩ cons y ys

      data _≋_ : Tree → Tree → Set (a ⊔ ℓ) where
        sta : ∀ {x y} → x ≋⟨s⟩ y → sta x ≋ sta y
        dyn : ∀ {x y} → x ≋⟨d⟩ y → dyn x ≋ dyn y

    mutual

      ≋⟨s⟩-refl : ∀ {x} → x ≋⟨s⟩ x
      ≋⟨s⟩-refl {leaf x}    = leaf A.refl
      ≋⟨s⟩-refl {cons x xs} = cons A.refl ≋⟨d⟩-refl

      ≋⟨d⟩-refl : ∀ {x} → x ≋⟨d⟩ x
      ≋⟨d⟩-refl {leaf x}    = leaf PE.refl
      ≋⟨d⟩-refl {cons x xs} = cons PE.refl ≋-refl

      ≋-refl : ∀ {x} → x ≋ x
      ≋-refl {sta x} = sta ≋⟨s⟩-refl
      ≋-refl {dyn x} = dyn ≋⟨d⟩-refl

    mutual

      ≋⟨s⟩-sym : ∀ {x y} → x ≋⟨s⟩ y → y ≋⟨s⟩ x
      ≋⟨s⟩-sym (leaf p)    = leaf (A.sym p)
      ≋⟨s⟩-sym (cons p ps) = cons (A.sym p) (≋⟨d⟩-sym ps)

      ≋⟨d⟩-sym : ∀ {x y} → x ≋⟨d⟩ y → y ≋⟨d⟩ x
      ≋⟨d⟩-sym (leaf p)    = leaf (PE.sym p)
      ≋⟨d⟩-sym (cons p ps) = cons (PE.sym p) (≋-sym ps)

      ≋-sym : ∀ {x y} → x ≋ y → y ≋ x
      ≋-sym (sta p) = sta (≋⟨s⟩-sym p)
      ≋-sym (dyn p) = dyn (≋⟨d⟩-sym p)

    mutual

      ≋⟨s⟩-trans : ∀ {x y z} → x ≋⟨s⟩ y → y ≋⟨s⟩ z → x ≋⟨s⟩ z
      ≋⟨s⟩-trans (leaf p)    (leaf q)    = leaf (A.trans p q)
      ≋⟨s⟩-trans (cons p ps) (cons q qs) = cons (A.trans p q) (≋⟨d⟩-trans ps qs)

      ≋⟨d⟩-trans : ∀ {x y z} → x ≋⟨d⟩ y → y ≋⟨d⟩ z → x ≋⟨d⟩ z
      ≋⟨d⟩-trans (leaf p)    (leaf q)    = leaf (PE.trans p q)
      ≋⟨d⟩-trans (cons p ps) (cons q qs) = cons (PE.trans p q) (≋-trans ps qs)

      ≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
      ≋-trans (sta p) (sta q) = sta (≋⟨s⟩-trans p q)
      ≋-trans (dyn p) (dyn q) = dyn (≋⟨d⟩-trans p q)

  ≋-isEquivalence : IsEquivalence _≋_
  ≋-isEquivalence = record { refl  = ≋-refl
                           ; sym   = ≋-sym
                           ; trans = ≋-trans
                           }

  Tree/≋ : Setoid _ _
  Tree/≋ = record { Carrier       = Tree
                  ; _≈_           = _≋_
                  ; isEquivalence = ≋-isEquivalence
                  }

  mutual

    _++⟨d⟩_ : DTree → Tree → DTree
    (leaf x)    ++⟨d⟩ y = cons x y
    (cons x xs) ++⟨d⟩ y = cons x (xs ++ y)

    _++_ : Tree → Tree → Tree
    sta (leaf x)    ++ sta (leaf y)    = sta (leaf (x · y))
    sta (leaf x)    ++ sta (cons y ys) = sta (cons (x · y) ys)
    sta (leaf x)    ++ dyn y           = sta (cons x y)
    sta (cons x xs) ++ y               = sta (cons x (xs ++⟨d⟩ y))
    dyn x           ++ y               = dyn (x ++⟨d⟩ y)

  mutual

    ++⟨d⟩-assoc : ∀ x y z → (x ++⟨d⟩ y) ++⟨d⟩ z ≋⟨d⟩ x ++⟨d⟩ (y ++ z)
    ++⟨d⟩-assoc (leaf x)    y z = ≋⟨d⟩-refl
    ++⟨d⟩-assoc (cons x xs) y z = cons PE.refl (++-assoc xs y z)

    ++-assoc : ∀ x y z → (x ++ y) ++ z ≋ x ++ (y ++ z)
    ++-assoc (sta (leaf x))    (sta (leaf y))    (sta (leaf z))    = sta (leaf (·-assoc x y z))
    ++-assoc (sta (leaf x))    (sta (leaf y))    (sta (cons z zs)) = sta (cons (·-assoc x y z) ≋⟨d⟩-refl)
    ++-assoc (sta (leaf x))    (sta (leaf y))    (dyn z)           = ≋-refl
    ++-assoc (sta (leaf x))    (sta (cons y ys)) z                 = ≋-refl
    ++-assoc (sta (leaf x))    (dyn y)           z                 = ≋-refl
    ++-assoc (sta (cons x xs)) y                 z                 = sta (cons A.refl (++⟨d⟩-assoc xs y z))
    ++-assoc (dyn x)           y                 z                 = dyn (++⟨d⟩-assoc x y z)

  mutual

    ++⟨d⟩-cong : ∀ {x y z w} → x ≋⟨d⟩ y → z ≋ w → x ++⟨d⟩ z ≋⟨d⟩ y ++⟨d⟩ w
    ++⟨d⟩-cong (leaf p)    q = cons p q
    ++⟨d⟩-cong (cons p ps) q = cons p (++-cong ps q)

    ++-cong : ∀ {x y z w} → x ≋ y → z ≋ w → x ++ z ≋ y ++ w
    ++-cong (sta (leaf p))    (sta (leaf q))    = sta (leaf (·-cong p q))
    ++-cong (sta (leaf p))    (sta (cons q qs)) = sta (cons (·-cong p q) qs)
    ++-cong (sta (leaf p))    (dyn q)           = sta (cons p q)
    ++-cong (sta (cons p ps)) q                 = sta (cons p (++⟨d⟩-cong ps q))
    ++-cong (dyn p)           q                 = dyn (++⟨d⟩-cong p q)

  Tree⟦_⟧ : Interpretation Tree/≋
  Tree⟦ • ⟧ (x ∷ y ∷ []) = x ++ y

  Tree⟦_⟧-cong : Congruence Tree/≋ Tree⟦_⟧
  Tree⟦ • ⟧-cong (p ∷ q ∷ []) = ++-cong p q

  Tree/≋-isAlgebra : IsAlgebra Tree/≋
  Tree/≋-isAlgebra = record { ⟦_⟧     = Tree⟦_⟧
                            ; ⟦⟧-cong = Tree⟦_⟧-cong
                            }

  Tree/≋-algebra : Algebra
  Tree/≋-algebra = record { ∥_∥/≈           = Tree/≋
                          ; ∥_∥/≈-isAlgebra = Tree/≋-isAlgebra
                          }

  Tree/≋-models : Models Tree/≋-algebra
  Tree/≋-models assoc θ = ++-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

  Tree/≋-isModel : IsModel Tree/≋
  Tree/≋-isModel = record { isAlgebra = Tree/≋-isAlgebra
                          ; models    = Tree/≋-models
                          }

  Frex : Model
  Frex = record { ∥_∥/≈   = Tree/≋
                ; isModel = Tree/≋-isModel
                }

  ∣inl∣ : ∥ A ∥ → ∥ Frex ∥
  ∣inl∣ x = sta (leaf x)

  ∣inl∣-cong : Congruent _≈_ _≋_ ∣inl∣
  ∣inl∣-cong p = sta (leaf p)

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

  inr : ∥ J n ∥ₐ ⟿ ∥ Frex ∥ₐ
  inr = interp Frex (λ k → dyn (leaf k))

  module _ {b ℓ} (X : Model {b} {ℓ}) where

    private

      open module X = Setoid ∥ X ∥/≈ renaming (_≈_ to _~_)

      _⊕_ : ∥ X ∥ → ∥ X ∥ → ∥ X ∥
      x ⊕ y = X ⟦ • ⟧ (x ∷ y ∷ [])

      ⊕-cong : ∀ {x y z w} → x ~ y → z ~ w → x ⊕ z ~ y ⊕ w
      ⊕-cong p q = (X ⟦ • ⟧-cong) (p ∷ q ∷ [])

      ⊕-assoc : ∀ (x y z : ∥ X ∥) → (x ⊕ y) ⊕ z ~ x ⊕ (y ⊕ z)
      ⊕-assoc x y z = ∥ X ∥ₐ-models assoc (env {A = ∥ X ∥ₐ} (x ∷ y ∷ z ∷ []))

    module _
      (f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ)
      (g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ)
      where

      ∣resid∣ : ∥ Frex ∥ → ∥ X ∥
      ∣resid∣ (sta (leaf x))    = ∣ f ∣ x
      ∣resid∣ (sta (cons x xs)) = ∣ f ∣ x ⊕ ∣resid∣ (dyn xs)
      ∣resid∣ (dyn (leaf x))    = ∣ g ∣ (atom (dyn x))
      ∣resid∣ (dyn (cons x xs)) = ∣ g ∣ (atom (dyn x)) ⊕ ∣resid∣ xs

      ∣resid∣-cong : Congruent _≋_ _~_ ∣resid∣
      ∣resid∣-cong (sta (leaf p))    = ∣ f ∣-cong p
      ∣resid∣-cong (sta (cons p ps)) = ⊕-cong (∣ f ∣-cong p) (∣resid∣-cong (dyn ps))
      ∣resid∣-cong (dyn (leaf p))    = ∣ g ∣-cong (inherit (atom (dyn p)))
      ∣resid∣-cong (dyn (cons p ps)) =
        ⊕-cong (∣ g ∣-cong (inherit (atom (dyn p)))) (∣resid∣-cong ps)

      open Reasoning ∥ X ∥/≈

      ∣resid∣-hom : Homomorphic ∥ Frex ∥ₐ ∥ X ∥ₐ ∣resid∣
      ∣resid∣-hom • (sta (leaf x) ∷ sta (leaf y) ∷ [])    = ∣ f ∣-hom • (x ∷ y ∷ [])
      ∣resid∣-hom • (sta (leaf x) ∷ sta (cons y ys) ∷ []) = begin
          ∣ f ∣ x ⊕ (∣ f ∣ y ⊕ ∣resid∣ (dyn ys))
        ≈⟨ X.sym (⊕-assoc (∣ f ∣ x) (∣ f ∣ y) _) ⟩
          (∣ f ∣ x ⊕ ∣ f ∣ y) ⊕ ∣resid∣ (dyn ys)
        ≈⟨ ⊕-cong (∣ f ∣-hom • (x ∷ y ∷ [])) X.refl ⟩
          ∣ f ∣ (x · y) ⊕ ∣resid∣ (dyn ys)
        ∎
      ∣resid∣-hom • (sta (leaf x) ∷ dyn y ∷ [])           = X.refl
      ∣resid∣-hom • (sta (cons x xs) ∷ y ∷ [])            = begin
          (∣ f ∣ x ⊕ ∣resid∣ (dyn xs)) ⊕ ∣resid∣ y
        ≈⟨ ⊕-assoc (∣ f ∣ x) _ (∣resid∣ y) ⟩
          ∣ f ∣ x ⊕ (∣resid∣ (dyn xs) ⊕ ∣resid∣ y)
        ≈⟨ ⊕-cong X.refl (∣resid∣-hom • (dyn xs ∷ y ∷ [])) ⟩
          ∣ f ∣ x ⊕ ∣resid∣ (dyn xs ++ y)
        ∎
      ∣resid∣-hom • (dyn (leaf x) ∷ y ∷ [])               = X.refl
      ∣resid∣-hom • (dyn (cons x xs) ∷ y ∷ [])            = begin
          (∣ g ∣ (atom (dyn x)) ⊕ ∣resid∣ xs) ⊕ ∣resid∣ y
        ≈⟨ ⊕-assoc _ (∣resid∣ xs) (∣resid∣ y) ⟩
          ∣ g ∣ (atom (dyn x)) ⊕ (∣resid∣ xs ⊕ ∣resid∣ y)
        ≈⟨ ⊕-cong X.refl (∣resid∣-hom • (xs ∷ y ∷ [])) ⟩
          ∣ g ∣ (atom (dyn x)) ⊕ ∣resid∣ (xs ++ y)
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

      ⊕-assoc : ∀ (x y z : ∥ X ∥) → (x ⊕ y) ⊕ z ~ x ⊕ (y ⊕ z)
      ⊕-assoc x y z = ∥ X ∥ₐ-models assoc (env {A = ∥ X ∥ₐ} (x ∷ y ∷ z ∷ []))

    module _
      {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
      {g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ}
      where

      commute₁ : X [ f , g ] ⊙ inl ≗ f
      commute₁ = X.refl

      open Reasoning ∥ X ∥/≈

      commute₂ : X [ f , g ] ⊙ inr ≗ g
      commute₂ {atom (dyn k)} =
        ∣ X [ f , g ] ∣-cong (≋-refl {x = dyn (leaf k)})
      commute₂ {t@(term • (x ∷ y ∷ []))} = begin
          ∣ X [ f , g ] ∣ (∣ inr ∣ t)
        ≈⟨ ∣ X [ f , g ] ∣-cong (∣ inr ∣-hom • (x ∷ y ∷ [])) ⟩
          ∣ X [ f , g ] ∣ (∣ inr ∣ x ++ ∣ inr ∣ y)
        ≈⟨ X.sym (∣ X [ f , g ] ∣-hom • (∣ inr ∣ x ∷ ∣ inr ∣ y ∷ [])) ⟩
          ∣ X [ f , g ] ∣ (∣ inr ∣ x) ⊕ ∣ X [ f , g ] ∣ (∣ inr ∣ y)
        ≈⟨ ⊕-cong commute₂ commute₂ ⟩
          ∣ g ∣ x ⊕ ∣ g ∣ y
        ≈⟨ ∣ g ∣-hom • (x ∷ y ∷ []) ⟩
          ∣ g ∣ t
        ∎

      module _ {h : ∥ Frex ∥ₐ ⟿ ∥ X ∥ₐ}
        (c₁ : h ⊙ inl ≗ f)
        (c₂ : h ⊙ inr ≗ g)
        where

        universal : X [ f , g ] ≗ h
        universal {sta (leaf x)}    = X.sym c₁
        universal {dyn (leaf x)}    = X.sym c₂
        universal {sta (cons x xs)} = begin
            ∣ f ∣ x ⊕ ∣ X [ f , g ] ∣ (dyn xs)
          ≈⟨ ⊕-cong (X.sym c₁) universal ⟩
            ∣ h ∣ (sta (leaf x)) ⊕ ∣ h ∣ (dyn xs)
          ≈⟨ ∣ h ∣-hom • (sta (leaf x) ∷ dyn xs ∷ []) ⟩
            ∣ h ∣ (sta (leaf x) ++ dyn xs)
          ∎
        universal {dyn (cons x xs)} = begin
            ∣ g ∣ (atom (dyn x)) ⊕ ∣ X [ f , g ] ∣ xs
          ≈⟨ ⊕-cong (X.sym c₂) universal ⟩
            ∣ h ∣ (dyn (leaf x)) ⊕ ∣ h ∣ xs
          ≈⟨ ∣ h ∣-hom • (dyn (leaf x) ∷ xs ∷ []) ⟩
            ∣ h ∣ (dyn (leaf x) ++ xs)
          ∎

SemigroupFrex : FreeExtension
SemigroupFrex = record { _[_]        = Frex
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
