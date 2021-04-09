{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.FreeExtension (Θ : Theory) where

open import Fragment.Equational.Model Θ
open import Fragment.Equational.FreeModel Θ
open import Fragment.Equational.Coproduct Θ

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Algebra (Σ Θ) using (Algebra)
open import Fragment.Algebra.TermAlgebra (Σ Θ) using (term)
open import Fragment.Algebra.TermAlgebra using (Expr)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.Homomorphism.Setoid (Σ Θ)
open import Fragment.Algebra.FreeAlgebra (Σ Θ)
  using (Environment; term₁; term₂; subst; subst-args)

open import Level using (Level; Setω)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)
open import Relation.Binary using (Setoid)

private
  variable
    a b ℓ₁ ℓ₂ : Level

IsFreeExtension : Model {a} {ℓ₁} → ℕ → Model {b} {ℓ₂} → Setω
IsFreeExtension M n N = IsCoproduct M |T|⦉ n ⦊/≈ₘ N

module _
  {M : Model {a} {ℓ₁}}
  {FX : Model {b} {ℓ₂}}
  {n : ℕ}
  (isFrex : IsFreeExtension M n FX)
  where

  open Setoid ∥ M ∥/≈
  open Setoid ∥ FX ∥/≈ using () renaming (_≈_ to _≈ₓ_)

  open IsCoproduct isFrex

  -- The following make the macro implementation slightly less painful

  FX-inl : ∥ M ∥ → ∥ FX ∥
  FX-inl = ∥ inl ∥ₕ

  FX-inr : Fin n → ∥ FX ∥
  FX-inr n = ∥ inr ∥ₕ (term₂ n)

  ∥FX∥ : Set _
  ∥FX∥ = ∥ FX ∥

  ∥FX∥ₐ : Algebra
  ∥FX∥ₐ = ∥ FX ∥ₐ

  reduceₕ : (θ : Environment n ∥ M ∥ₐ) → ∥ FX ∥ₐ →ₕ ∥ M ∥ₐ
  reduceₕ θ = ([_,_] {W = M} (idₕ ∥ M ∥ₐ) (substₕ M θ))

  reduce : (θ : Environment n ∥ M ∥ₐ) → ∥ FX ∥ → ∥ M ∥
  reduce θ x = ∥ reduceₕ θ ∥ₕ x

  open import Relation.Binary.Reasoning.Setoid ∥ M ∥/≈

  mutual
    factor-args : ∀ {arity m}
                  → (θ : Environment m ∥ M ∥ₐ)
                  → (η : Environment m ∥ FX ∥ₐ)
                  → (ψ : Environment n ∥ M ∥ₐ)
                  → (∀ {k} → reduce ψ (η k) ≈ θ k)
                  → ∀ {xs : Vec (Expr ((Σ Θ) ⦉ m ⦊)) arity}
                  → Pointwise _≈_ (map (reduce ψ) (subst-args ∥ FX ∥ₐ η xs)) (subst-args ∥ M ∥ₐ θ xs)
    factor-args θ η ψ p {[]}     = []
    factor-args θ η ψ p {x ∷ xs} = (factor θ η ψ p {x = x}) ∷ (factor-args θ η ψ p {xs = xs})

    factor : ∀ {m}
             → (θ : Environment m ∥ M ∥ₐ)
             → (η : Environment m ∥ FX ∥ₐ)
             → (ψ : Environment n ∥ M ∥ₐ)
             → (∀ {k} → reduce ψ (η k) ≈ θ k)
             → reduceₕ ψ ∘ₕ (substₕ FX η) ≡ₕ substₕ M θ
    factor θ η ψ p {term₂ k} = p
    factor θ η ψ p {term₁ f} = sym (∥ reduceₕ ψ ∥ₕ-hom f [])
    factor θ η ψ p {term f (x ∷ xs)}  = begin
        reduce ψ ((FX ⟦ f ⟧) (subst-args ∥ FX ∥ₐ η (x ∷ xs)))
      ≈⟨ sym (∥ reduceₕ ψ ∥ₕ-hom f (subst-args ∥ FX ∥ₐ η (x ∷ xs))) ⟩
        (M ⟦ f ⟧) (map (reduce ψ) (subst-args ∥ FX ∥ₐ η (x ∷ xs)))
      ≈⟨ (M ⟦⟧-cong) f (factor-args θ η ψ p {xs = x ∷ xs}) ⟩
        (M ⟦ f ⟧) (subst-args ∥ M ∥ₐ θ (x ∷ xs))
      ∎

  fundamental : ∀ {x y : ∥ M ∥} {x' y' : ∥ FX ∥}
                → (θ : Environment n ∥ M ∥ₐ)
                → reduce θ x' ≈ x
                → reduce θ y' ≈ y
                → x' ≈ₓ y'
                → x ≈ y
  fundamental θ p q x'≈ₓy' = trans (trans (sym p) (∥ reduceₕ θ ∥ₕ-cong x'≈ₓy')) q
