{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension.Synthetic (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra (Σ Θ) using (Algebra)
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
import Relation.Binary.Reasoning.Setoid as Reasoning
import Relation.Binary.PropositionalEquality as PE

private
  variable
    a b ℓ₁ ℓ₂ ℓ₃ : Level

  module _ (A : Model {a} {ℓ₁}) (n : ℕ) where

    Terms : Algebra
    Terms = Free (Atoms ∥ A ∥/≈ n)

    open module T = Setoid Algebra.∥ Terms ∥/≈ renaming (_≈_ to _~_) using ()

    ∣inl∣ : ∥ A ∥ → T.Carrier
    ∣inl∣ x = atom (sta x)

    infix 4 _≈_

    data _≈_ : T.Carrier → T.Carrier → Set (a ⊔ ℓ₁) where
      refl     : ∀ {x} → x ≈ x
      sym      : ∀ {x y} → x ≈ y → y ≈ x
      trans    : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
      inherit  : ∀ {x y} → x ~ y → x ≈ y
      evaluate : ∀ {n xs} → (f : ops (Σ Θ) n)
                 → term f (map ∣inl∣ xs) ≈ ∣inl∣ (A ⟦ f ⟧ xs)
      cong     : ∀ {n} → (f : ops (Σ Θ) n)
                 → ∀ {xs ys} → Pointwise _≈_ xs ys
                 → term f xs ≈ term f ys
      axiom    : ∀ {n} → (eq : eqs Θ n) → (θ : Env Terms n)
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

    module N = Setoid (∥ Terms ∥/ _≈_)

    Syn-models : Models (Terms / _≈_)
    Syn-models eq θ = begin
        ∣ inst (Terms / _≈_) θ ∣ lhs
      ≈⟨ N.sym (lemma {x = lhs}) ⟩
        ∣ inst Terms θ ∣ lhs
      ≈⟨ axiom eq θ ⟩
        ∣ inst Terms θ ∣ rhs
      ≈⟨ lemma {x = rhs} ⟩
        ∣ inst (Terms / _≈_) θ ∣ rhs
      ∎
      where open Reasoning (∥ Terms ∥/ _≈_)

            lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
            rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

            lemma = inst-universal (Terms / _≈_) θ
                      {h = (inc Terms _≈_) ⊙ (inst Terms θ) }
                      (λ x → PE.refl)

    Syn-isModel : IsModel (∥ Terms ∥/ _≈_)
    Syn-isModel = record { isAlgebra = Terms / _≈_ -isAlgebra
                         ; models    = Syn-models
                         }

    Syn : Model
    Syn = record { ∥_∥/≈   = ∥ Terms ∥/ _≈_
                 ; isModel = Syn-isModel
                 }

    ∣inl∣-cong : Congruent ≈[ A ] _≈_ ∣inl∣
    ∣inl∣-cong p = inherit (atom (sta p))

    ∣inl∣-hom : Homomorphic ∥ A ∥ₐ ∥ Syn ∥ₐ ∣inl∣
    ∣inl∣-hom f xs = evaluate f

    ∣inl∣⃗ : ∥ A ∥/≈ ↝ ∥ Syn ∥/≈
    ∣inl∣⃗ = record { ∣_∣      = ∣inl∣
                    ; ∣_∣-cong = ∣inl∣-cong
                    }

    inl : ∥ A ∥ₐ ⟿ ∥ Syn ∥ₐ
    inl = record { ∣_∣⃗    = ∣inl∣⃗
                 ; ∣_∣-hom = ∣inl∣-hom
                 }

    inr : ∥ J n ∥ₐ ⟿ ∥ Syn ∥ₐ
    inr = interp Syn (λ n → atom (dyn n))

    module _
      (X : Model {b} {ℓ₂})
      (f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ)
      (g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ)
      where

      private module X = Setoid ∥ X ∥/≈
      open Reasoning ∥ X ∥/≈

      resid : Terms ⟿ ∥ X ∥ₐ
      resid = subst ∥ X ∥ₐ ∣ f ∣⃗ (λ n → ∣ g ∣ (atom (dyn n)))

      ∣resid∣-map-∣inl∣ : ∀ {m} {xs : Vec ∥ A ∥ m}
                          → Pointwise ≈[ X ]
                                      (map ∣ resid ∣ (map ∣inl∣ xs))
                                      (map ∣ f ∣ xs)
      ∣resid∣-map-∣inl∣ {xs = []}     = []
      ∣resid∣-map-∣inl∣ {xs = x ∷ xs} = X.refl ∷ ∣resid∣-map-∣inl∣

      mutual
        ∣resid∣-args-cong : ∀ {m} {xs ys : Vec ∥ Syn ∥ m}
                            → Pointwise _≈_ xs ys
                            → Pointwise ≈[ X ] (map ∣ resid ∣ xs)
                                               (map ∣ resid ∣ ys)
        ∣resid∣-args-cong []       = []
        ∣resid∣-args-cong (p ∷ ps) = ∣resid∣-cong p ∷ ∣resid∣-args-cong ps

        ∣resid∣-cong : Congruent _≈_ ≈[ X ] ∣ resid ∣
        ∣resid∣-cong refl        = X.refl
        ∣resid∣-cong (sym p)     = X.sym (∣resid∣-cong p)
        ∣resid∣-cong (trans p q) = X.trans (∣resid∣-cong p) (∣resid∣-cong q)
        ∣resid∣-cong (inherit p) = ∣ resid ∣-cong p
        ∣resid∣-cong (evaluate {xs = xs} op) = begin
            ∣ resid ∣ (term op (map ∣inl∣ xs))
          ≈⟨ X.sym (∣ resid ∣-hom op (map ∣inl∣ xs)) ⟩
            X ⟦ op ⟧ (map ∣ resid ∣ (map ∣inl∣ xs))
          ≈⟨ (X ⟦ op ⟧-cong) ∣resid∣-map-∣inl∣ ⟩
            X ⟦ op ⟧ (map ∣ f ∣ xs)
          ≈⟨ ∣ f ∣-hom op xs ⟩
            ∣ f ∣ (A ⟦ op ⟧ xs)
          ∎
        ∣resid∣-cong (cong f {xs = xs} {ys = ys} ps) = begin
            ∣ resid ∣ (term f xs)
          ≈⟨ X.sym (∣ resid ∣-hom f xs) ⟩
            X ⟦ f ⟧ (map ∣ resid ∣ xs)
          ≈⟨ (X ⟦ f ⟧-cong) (∣resid∣-args-cong ps) ⟩
            X ⟦ f ⟧ (map ∣ resid ∣ ys)
          ≈⟨ ∣ resid ∣-hom f ys ⟩
            ∣ resid ∣ (term f ys)
          ∎
        ∣resid∣-cong (axiom eq θ) = begin
            ∣ resid ∣ (∣ inst Terms θ ∣ lhs)
          ≈⟨ inst-assoc Terms θ resid {lhs} ⟩
            ∣ inst ∥ X ∥ₐ (∣ resid ∣ ∘ θ) ∣ lhs
          ≈⟨ ∥ X ∥ₐ-models eq (∣ resid ∣ ∘ θ) ⟩
            ∣ inst ∥ X ∥ₐ (∣ resid ∣ ∘ θ) ∣ rhs
          ≈⟨ X.sym (inst-assoc Terms θ resid {rhs}) ⟩
            ∣ resid ∣ (∣ inst Terms θ ∣ rhs)
          ∎
          where lhs = proj₁ (Θ ⟦ eq ⟧ₑ)
                rhs = proj₂ (Θ ⟦ eq ⟧ₑ)

      _[_,_] : ∥ Syn ∥ₐ ⟿ ∥ X ∥ₐ
      _[_,_] = factor Terms _≈_ resid ∣resid∣-cong

    module _
      {X : Model {b} {ℓ₂}}
      {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
      {g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ}
      where

      private module X = Setoid ∥ X ∥/≈
      open Reasoning ∥ X ∥/≈

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
        {h : ∥ Syn ∥ₐ ⟿ ∥ X ∥ₐ}
        (c₁ : h ⊙ inl ≗ f)
        (c₂ : h ⊙ inr ≗ g)
        where

        mutual
          map-universal : ∀ {m} {xs : Vec ∥ Syn ∥ m}
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

    isFrex : IsCoproduct A (J n) Syn
    isFrex =
      record { inl       = inl
             ; inr       = inr
             ; _[_,_]    = _[_,_]
             ; commute₁  = λ {_ _ X f g} → commute₁ {X = X} {f} {g}
             ; commute₂  = λ {_ _ X f g} → commute₂ {X = X} {f} {g}
             ; universal = λ {_ _ X f g h} → universal {X = X} {f} {g} {h}
             }

SynFrex : FreeExtension
SynFrex = record { _[_]        = Syn
                 ; _[_]-isFrex = isFrex
                 }
