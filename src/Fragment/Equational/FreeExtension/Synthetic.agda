{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension.Synthetic (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra (Σ Θ) as Algebra using (Algebra)
open import Fragment.Equational.Model Θ
open import Fragment.Equational.Coproduct Θ
open import Fragment.Equational.FreeExtension.Base Θ
open import Fragment.Algebra.Free (Σ Θ)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Quotient (Σ Θ)
open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ : Level

module _ (A : Model {a} {ℓ₁}) (n : ℕ) where

  private
    Terms : Algebra
    Terms = Free (Atoms ∥ A ∥/≈ n)

  open Setoid Algebra.∥ Terms ∥/≈
    renaming (Carrier to Q; _≈_ to _~_)
    using ()

  ∣inl∣ : ∥ A ∥ → Q
  ∣inl∣ x = atom (sta x)

  infix 4 _≈_

  data _≈_ : Q → Q → Set (a ⊔ ℓ₁) where
    refl    : ∀ {x} → x ≈ x
    sym     : ∀ {x y} → x ≈ y → y ≈ x
    trans   : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
    inherit : ∀ {x y} → x ~ y → x ≈ y
    step    : ∀ {n xs} → (f : ops (Σ Θ) n)
              → term f (map ∣inl∣ xs) ≈ ∣inl∣ (A ⟦ f ⟧ xs)
    cong    : ∀ {n} → (f : ops (Σ Θ) n)
              → ∀ {xs ys} → Pointwise _≈_ xs ys
              → term f xs ≈ term f ys
    model   : ∀ {n} → (eq : eqs Θ n) → (θ : Env Terms n)
              → ∣ inst Terms θ ∣ (proj₁ (Θ ⟦ eq ⟧ₑ))
                ≈ ∣ inst Terms θ ∣ (proj₂ (Θ ⟦ eq ⟧ₑ))

  ≈-isEquivalence : IsEquivalence _≈_
  ≈-isEquivalence = record { refl  = refl
                           ; sym   = sym
                           ; trans = trans
                           }

  instance
    ≈-isDenom : IsDenominator Terms _≈_
    ≈-isDenom = record { isEquivalence = ≈-isEquivalence
                       ; isCompatible  = cong
                       ; isCoarser     = inherit
                       }

  open module N = Setoid (∥ Terms ∥/ _≈_) using ()
  open import Relation.Binary.Reasoning.Setoid (∥ Terms ∥/ _≈_)

  Normals-models : Models (Terms / _≈_)
  Normals-models eq θ = begin
      ∣ inst (Terms / _≈_) θ ∣ lhs
    ≡⟨ PE.sym (∣inst∣-quot _≈_ {x = lhs} θ) ⟩
      ∣ inst Terms θ ∣ lhs
    ≈⟨ model eq θ ⟩
      ∣ inst Terms θ ∣ rhs
    ≡⟨ ∣inst∣-quot _≈_ {x = rhs} θ ⟩
      ∣ inst (Terms / _≈_) θ ∣ rhs
    ∎
    where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
          rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

  Normals-isModel : IsModel (∥ Terms ∥/ _≈_)
  Normals-isModel = record { isAlgebra = Terms / _≈_ -isAlgebra
                           ; models    = Normals-models
                           }

  Normals : Model
  Normals = record { ∥_∥/≈   = ∥ Terms ∥/ _≈_
                   ; isModel = Normals-isModel
                   }

  ∣inl∣-cong : Congruent ≈[ A ] _≈_ ∣inl∣
  ∣inl∣-cong p = inherit (atom (sta p))

  ∣inl∣-hom : Homomorphic ∥ A ∥ₐ ∥ Normals ∥ₐ ∣inl∣
  ∣inl∣-hom f xs = step f

  ∣inl∣⃗ : ∥ A ∥/≈ ↝ ∥ Normals ∥/≈
  ∣inl∣⃗ = record { ∣_∣      = ∣inl∣
                  ; ∣_∣-cong = ∣inl∣-cong
                  }

  inl : ∥ A ∥ₐ ⟿ ∥ Normals ∥ₐ
  inl = record { ∣_∣⃗    = ∣inl∣⃗
               ; ∣_∣-hom = ∣inl∣-hom
               }

  inr : ∥ J n ∥ₐ ⟿ ∥ Normals ∥ₐ
  inr = interp Normals λ n → atom (dyn n)

  module _
    (X : Model {b} {ℓ₂})
    (f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ)
    (g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ)
    where

    private
      module X = Setoid ∥ X ∥/≈

      s : Terms ⟿ ∥ X ∥ₐ
      s = subst ∥ X ∥ₐ ∣ f ∣⃗ (∣ g ∣ ∘ atom)

      s-cong : Congruent _≈_ ≈[ X ] ∣ s ∣
      s-cong refl         = X.refl
      s-cong (sym p)      = X.sym (s-cong p)
      s-cong (trans p q)  = X.trans (s-cong p) (s-cong q)
      s-cong (inherit p)  = ∣ s ∣-cong p
      s-cong (step f)     = {!!}
      s-cong (cong f ps)  = {!!}
      s-cong (model eq θ) = {!!}

    _[_,_] : ∥ Normals ∥ₐ ⟿ ∥ X ∥ₐ
    _[_,_] = factor Terms _≈_ s s-cong

{-
  module _
    {X : Model {b} {ℓ₂}}
    {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
    {g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ}
    where

    module X = Setoid ∥ X ∥/≈

    commute₁ : X [ f , g ] ⊙ inl ≗ f
    commute₁ {x} = X.refl

    commute₂ : X [ f , g ] ⊙ inr ≗ g
    commute₂ {x} = {!!}

    module _
      {h : ∥ Normals ∥ₐ ⟿ ∥ X ∥ₐ}
      (c₁ : h ⊙ inl ≗ f)
      (c₁ : h ⊙ inr ≗ g)
      where

      universal : X [ f , g ] ≗ h
      universal = {!!}

  isFrex : IsCoproduct A (J n) Normals
  isFrex = record { inl       = inl
                  ; inr       = inr
                  ; _[_,_]    = _[_,_]
                  ; commute₁  = commute₁
                  ; commute₂  = commute₂
                  ; universal = universal
                  }
-}
