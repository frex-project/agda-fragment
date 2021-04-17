{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension.Synthetic (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra (Σ Θ) as Algebra using (Algebra)
open import Fragment.Equational.FreeExtension.Base Θ
open import Fragment.Equational.Model Θ
open import Fragment.Algebra.Free (Σ Θ)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Quotient (Σ Θ)
open import Fragment.Setoid.Morphism using (lift; _↝_)

open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using (map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)

open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a ℓ : Level

module _ (A : Model {a} {ℓ}) (n : ℕ) where

  private
    Terms : Algebra
    Terms = Free (Atoms ∥ A ∥/≈ n)

  open Setoid Algebra.∥ Terms ∥/≈
    renaming (Carrier to Q; _≈_ to _~_)
    using ()

  ∣inl∣ : ∥ A ∥ → Q
  ∣inl∣ x = atom (sta x)

  ∣inr∣ : ∥ J n ∥ → Q
  ∣inr∣ = ∣ fold Terms (lift (λ x → atom (dyn x))) ∣

  infix 4 _≈_

  data _≈_ : Q → Q → Set (a ⊔ ℓ) where
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

  ≋ : CompatibleEquivalence Terms
  ≋ = record { _≈_           = _≈_
             ; isEquivalence = ≈-isEquivalence
             ; compatible    = cong
             }

  open module N = Setoid (setoid ≋) using ()
  open import Relation.Binary.Reasoning.Setoid (setoid ≋)

  Normals-models : Models (Terms / ≋)
  Normals-models eq θ = begin
      ∣ inst (Terms / ≋) θ ∣ lhs
    ≡⟨ PE.sym (∣inst∣-quot (≋) {x = lhs} θ) ⟩
      ∣ inst Terms θ ∣ lhs
    ≈⟨ model eq θ ⟩
      ∣ inst Terms θ ∣ rhs
    ≡⟨ ∣inst∣-quot (≋) {x = rhs} θ ⟩
      ∣ inst (Terms / ≋) θ ∣ rhs
    ∎
    where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
          rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

  Normals-isModel : IsModel (setoid ≋)
  Normals-isModel = record { isAlgebra = Terms / ≋ -isAlgebra
                           ; models    = Normals-models
                           }

  Normals : Model
  Normals = record { ∥_∥/≈   = setoid ≋
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
