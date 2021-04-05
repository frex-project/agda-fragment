{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension (Θ : Theory) where

open import Fragment.Equational.Model
open import Fragment.Equational.FreeModel
open import Fragment.Equational.Coproduct Θ

open import Fragment.Algebra.Algebra using (Algebra)
open import Fragment.Algebra.TermAlgebra
open import Fragment.Algebra.FreeAlgebra using (Environment; subst; subst-args)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ)
open import Fragment.Algebra.Signature renaming (_⦉_⦊ to _⦉_⦊ₜ)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using ([]; _∷_)
open import Level using (Level; Setω)

private
  variable
    a b ℓ₁ ℓ₂ : Level

IsFreeExtension : Model Θ {a} {ℓ₁} → ℕ → Model Θ {b} {ℓ₂} → Setω
IsFreeExtension M n N = IsCoproduct M (|T|ₘ Θ ⦉ n ⦊) N

module _
  {M : Model Θ {a} {ℓ₁}}
  {F : Model Θ {b} {ℓ₂}}
  {n : ℕ}
  (F-frex : IsFreeExtension M n F)
  where

  open Model M renaming (Carrierₐ to S; Carrier to A; trans to M-trans; sym to M-sym)
  open Model F renaming (_≈_ to _≈ₓ_; Carrierₐ to FXₐ; Carrier to FX; ⟦_⟧ to ⟦_⟧ₓ)
    hiding (⟦⟧-cong)
  open IsCoproduct F-frex

  FXinl : A → FX
  FXinl = applyₕ inl

  FXinr : Fin n → FX
  FXinr n = applyₕ inr (term (inj₂ n) [])

  FXcarrier : Set _
  FXcarrier = FX

  FXalgebra : Algebra (Σ Θ)
  FXalgebra = FXₐ

  reduceₕ : (θ : Environment n S) → FXₐ →ₕ S
  reduceₕ θ = ([_,_] {W = M} (idₕ S) (substₕ M θ))

  reduce : (θ : Environment n S) → FX → A
  reduce θ x = applyₕ (reduceₕ θ) x

  open import Relation.Binary.Reasoning.Setoid (Model.Carrierₛ M)

  mutual
    factor-args : ∀ {arity m}
                  → (θ : Environment m S)
                  → (η : Environment m FXₐ)
                  → (ψ : Environment n S)
                  → (∀ {k} → reduce ψ (η k) ≈ θ k)
                  → ∀ {xs : Vec (Expr ((Σ Θ) ⦉ m ⦊ₜ)) arity}
                  → PW.Pointwise _≈_ (map (reduce ψ) (subst-args FXₐ η xs)) (subst-args S θ xs)
    factor-args θ η ψ p {[]}     = []
    factor-args θ η ψ p {x ∷ xs} = (factor θ η ψ p {x = x}) ∷ (factor-args θ η ψ p {xs = xs})

    factor : ∀ {m}
             → (θ : Environment m S)
             → (η : Environment m FXₐ)
             → (ψ : Environment n S)
             → (∀ {k} → reduce ψ (η k) ≈ θ k)
             → reduceₕ ψ ∘ₕ (substₕ F η) ≡ₕ substₕ M θ
    factor θ η ψ p {term (inj₂ k) []} = p
    factor θ η ψ p {term (inj₁ f) []} = M-sym (reduce-hom f [])
        where open _→ₕ_ (reduceₕ ψ) renaming (h-hom to reduce-hom)
    factor θ η ψ p {term f (x ∷ xs)}  = begin
        reduce ψ (subst FXₐ η (term f (x ∷ xs)))
      ≡⟨⟩
        reduce ψ (⟦ f ⟧ₓ (subst-args FXₐ η (x ∷ xs)))
      ≈⟨ M-sym (reduce-hom f (subst-args FXₐ η (x ∷ xs))) ⟩
        ⟦ f ⟧ (map (reduce ψ) (subst-args FXₐ η (x ∷ xs)))
      ≈⟨ ⟦⟧-cong f (factor-args θ η ψ p {xs = x ∷ xs}) ⟩
        ⟦ f ⟧ (subst-args S θ (x ∷ xs))
       ≡⟨⟩
        subst S θ (term f (x ∷ xs))
      ∎
      where open _→ₕ_ (reduceₕ ψ) renaming (h-hom to reduce-hom)

  fundamental : ∀ {x y : A} {x' y' : FX}
                → (θ : Environment n S)
                → reduce θ x' ≈ x
                → reduce θ y' ≈ y
                → x' ≈ₓ y'
                → x ≈ y
  fundamental θ p q x'≈ₓy' = M-trans (M-trans (M-sym p) (_→ₕ_.h-cong (reduceₕ θ) x'≈ₓy')) q
