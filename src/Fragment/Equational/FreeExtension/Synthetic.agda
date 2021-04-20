{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension.Synthetic (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra (Σ Θ) as Algebra using (Algebra)
open import Fragment.Equational.Model Θ
open import Fragment.Equational.Coproduct Θ
open import Fragment.Equational.FreeExtension.Base Θ
open import Fragment.Algebra.Free (Σ Θ) hiding (_~_)
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
    axiom   : ∀ {n} → (eq : eqs Θ n) → (θ : Env Terms n)
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

  Normals-models : Models (Terms / _≈_)
  Normals-models eq θ = begin
      ∣ inst (Terms / _≈_) θ ∣ lhs
    ≈⟨ N.sym (inst-universal (Terms / _≈_) θ
                             {h = (inc Terms _≈_) ⊙ (inst Terms θ) }
                             (λ x → PE.refl) {x = lhs})
     ⟩
      ∣ inst Terms θ ∣ lhs
    ≈⟨ axiom eq θ ⟩
      ∣ inst Terms θ ∣ rhs
    ≈⟨ inst-universal (Terms / _≈_) θ
                      {h = (inc Terms _≈_) ⊙ (inst Terms θ) }
                      (λ x → PE.refl) {x = rhs}
     ⟩
      ∣ inst (Terms / _≈_) θ ∣ rhs
    ∎
    where open import Relation.Binary.Reasoning.Setoid (∥ Terms ∥/ _≈_)
          lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
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

    open import Relation.Binary.Reasoning.Setoid ∥ X ∥/≈

    private

      module X = Setoid ∥ X ∥/≈

      ∣g∣ : Fin n → ∥ X ∥
      ∣g∣ n = ∣ g ∣ (atom (dyn n))

      s : Terms ⟿ ∥ X ∥ₐ
      s = subst ∥ X ∥ₐ ∣ f ∣⃗ ∣g∣

      ∣s∣-map-∣inl∣ : ∀ {m} {xs : Vec ∥ A ∥ m}
                      → Pointwise ≈[ X ]
                                  (map ∣ s ∣ (map ∣inl∣ xs))
                                  (map ∣ f ∣ xs)
      ∣s∣-map-∣inl∣ {xs = []}     = []
      ∣s∣-map-∣inl∣ {xs = x ∷ xs} = X.refl ∷ ∣s∣-map-∣inl∣

      mutual
        ∣s∣-args-cong : ∀ {m} {xs ys : Vec ∥ Normals ∥ m}
                        → Pointwise _≈_ xs ys
                        → Pointwise ≈[ X ] (map ∣ s ∣ xs) (map ∣ s ∣ ys)
        ∣s∣-args-cong []       = []
        ∣s∣-args-cong (p ∷ ps) = s-cong p ∷ ∣s∣-args-cong ps

        s-cong : Congruent _≈_ ≈[ X ] ∣ s ∣
        s-cong refl        = X.refl
        s-cong (sym p)     = X.sym (s-cong p)
        s-cong (trans p q) = X.trans (s-cong p) (s-cong q)
        s-cong (inherit p) = ∣ s ∣-cong p
        s-cong (step {xs = xs} op) = begin
            ∣ s ∣ (term op (map ∣inl∣ xs))
          ≈⟨ X.sym (∣ s ∣-hom op (map ∣inl∣ xs)) ⟩
            X ⟦ op ⟧ (map ∣ s ∣ (map ∣inl∣ xs))
          ≈⟨ (X ⟦ op ⟧-cong) ∣s∣-map-∣inl∣ ⟩
            X ⟦ op ⟧ (map ∣ f ∣ xs)
          ≈⟨ ∣ f ∣-hom op xs ⟩
            ∣ f ∣ (A ⟦ op ⟧ xs)
          ∎
        s-cong (cong f {xs = xs} {ys = ys} ps) = begin
            ∣ s ∣ (term f xs)
          ≈⟨ X.sym (∣ s ∣-hom f xs) ⟩
            X ⟦ f ⟧ (map ∣ s ∣ xs)
          ≈⟨ (X ⟦ f ⟧-cong) (∣s∣-args-cong ps) ⟩
            X ⟦ f ⟧ (map ∣ s ∣ ys)
          ≈⟨ ∣ s ∣-hom f ys ⟩
            ∣ s ∣ (term f ys)
          ∎
        s-cong (axiom eq θ) = begin
            ∣ s ∣ (∣ inst Terms θ ∣ lhs)
          ≈⟨ inst-assoc Terms θ s {lhs} ⟩
            ∣ inst ∥ X ∥ₐ (∣ s ∣ ∘ θ) ∣ lhs
          ≈⟨ ∥ X ∥ₐ-models eq (∣ s ∣ ∘ θ) ⟩
            ∣ inst ∥ X ∥ₐ (∣ s ∣ ∘ θ) ∣ rhs
          ≈⟨ X.sym (inst-assoc Terms θ s {rhs}) ⟩
            ∣ s ∣ (∣ inst Terms θ ∣ rhs)
          ∎
          where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
                rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

    _[_,_] : ∥ Normals ∥ₐ ⟿ ∥ X ∥ₐ
    _[_,_] = factor Terms _≈_ s s-cong

  module _
    {X : Model {b} {ℓ₂}}
    {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
    {g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ}
    where

    module X = Setoid ∥ X ∥/≈
    open import Relation.Binary.Reasoning.Setoid ∥ X ∥/≈

    commute₁ : X [ f , g ] ⊙ inl ≗ f
    commute₁ = X.refl

    mutual
      map-commute₂ : ∀ {m} {xs : Vec ∥ J n ∥ m}
                     → Pointwise ≈[ X ]
                                 (map ∣ X [ f , g ] ⊙ inr ∣ xs)
                                 (map ∣ g ∣ xs)
      map-commute₂ {xs = []}     = []
      map-commute₂ {xs = x ∷ xs} = commute₂ ∷ map-commute₂

      commute₂ : X [ f , g ] ⊙ inr ≗ g
      commute₂ {atom (dyn _)} = X.refl
      commute₂ {term op xs}    = begin
          ∣ X [ f , g ] ⊙ inr ∣ (term op xs)
        ≈⟨ X.sym (∣ X [ f , g ] ⊙ inr ∣-hom op xs) ⟩
          X ⟦ op ⟧ (map ∣ X [ f , g ] ⊙ inr ∣ xs)
        ≈⟨ (X ⟦ op ⟧-cong) map-commute₂ ⟩
          X ⟦ op ⟧ (map ∣ g ∣ xs)
        ≈⟨ ∣ g ∣-hom op xs ⟩
          ∣ g ∣ (term op xs)
        ∎

    module _
      {h : ∥ Normals ∥ₐ ⟿ ∥ X ∥ₐ}
      (c₁ : h ⊙ inl ≗ f)
      (c₂ : h ⊙ inr ≗ g)
      where

      mutual
        map-universal : ∀ {m} {xs : Vec ∥ Normals ∥ m}
                        → Pointwise ≈[ X ]
                                    (map ∣ X [ f , g ] ∣ xs)
                                    (map ∣ h ∣ xs)
        map-universal {xs = []}     = []
        map-universal {xs = x ∷ xs} = universal ∷ map-universal

        universal : X [ f , g ] ≗ h
        universal {atom (sta x)} = X.sym c₁
        universal {atom (dyn x)} = begin
            ∣ X [ f , g ] ∣ (atom (dyn x))
          ≈⟨ commute₂ ⟩
            ∣ g ∣ (atom (dyn x))
          ≈⟨ X.sym c₂ ⟩
            ∣ h ∣ (atom (dyn x))
          ∎
        universal {term op xs}   = begin
            ∣ X [ f , g ] ∣ (term op xs)
          ≈⟨ X.sym (∣ X [ f , g ] ∣-hom op xs) ⟩
            X ⟦ op ⟧ (map ∣ X [ f , g ] ∣ xs)
          ≈⟨ (X ⟦ op ⟧-cong) map-universal ⟩
            X ⟦ op ⟧ (map ∣ h ∣ xs)
          ≈⟨ ∣ h ∣-hom op xs ⟩
            ∣ h ∣ (term op xs)
          ∎

  isFrex : IsCoproduct A (J n) Normals
  isFrex =
    record { inl       = inl
           ; inr       = inr
           ; _[_,_]    = _[_,_]
           ; commute₁  = λ {_} {_} {X} {f} {g} → commute₁ {X = X} {f = f} {g = g}
           ; commute₂  = λ {_} {_} {X} {f} {g} → commute₂ {X = X} {f = f} {g = g}
           ; universal = λ {_} {_} {X} {f} {g} {h} → universal {X = X} {f = f} {g = g} {h = h}
           }

SynFrex : FreeExtension
SynFrex = record { _[_]        = Normals
                 ; _[_]-isFrex = isFrex
                 }
