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

open import Level using (Level; Setω; _⊔_)
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
    a ℓ : Level

Extension : Setω
Extension = ∀ {a} {ℓ} → Model {a} {ℓ} → ℕ → Model {a} {a ⊔ ℓ}

IsFreeExtension : Extension → Setω
IsFreeExtension FX =
  ∀ {a ℓ} (M : Model {a} {ℓ}) (n : ℕ) → IsCoproduct M |T|⦉ n ⦊/≈ₘ (FX M n)

record FreeExtension : Setω where
  field
    _[_]        : Extension
    _[_]-isFrex : IsFreeExtension _[_]

module _
  (FX : FreeExtension)
  (M : Model {a} {ℓ})
  (n : ℕ)
  where

  open FreeExtension FX

  open Setoid ∥ M ∥/≈
  open Setoid ∥ M [ n ] ∥/≈ using () renaming (_≈_ to _≈ₓ_)

  open IsCoproduct (M [ n ]-isFrex)

  -- The following make the macro implementation slightly less painful

  FX-inl : ∥ M ∥ → ∥ M [ n ] ∥
  FX-inl = ∥ inl ∥ₕ

  FX-inr : Fin n → ∥ M [ n ] ∥
  FX-inr n = ∥ inr ∥ₕ (term₂ n)

  ∥FX∥ : Set _
  ∥FX∥ = ∥ M [ n ] ∥

  ∥FX∥/≈ : Setoid _ _
  ∥FX∥/≈ = ∥ M [ n ] ∥/≈

  ∥FX∥ₐ : Algebra
  ∥FX∥ₐ = ∥ M [ n ] ∥ₐ

  reduceₕ : (θ : Environment n ∥ M ∥ₐ) → ∥ M [ n ] ∥ₐ →ₕ ∥ M ∥ₐ
  reduceₕ θ = ([_,_] {W = M} idₕ (substₕ M θ))

  reduce : (θ : Environment n ∥ M ∥ₐ) → ∥ M [ n ] ∥ → ∥ M ∥
  reduce θ = ∥ reduceₕ θ ∥ₕ

  open import Relation.Binary.Reasoning.Setoid ∥ M ∥/≈

  mutual
    factor-args : ∀ {arity m}
                  → (θ : Environment m ∥ M ∥ₐ)
                  → (η : Environment m ∥ M [ n ] ∥ₐ)
                  → (ψ : Environment n ∥ M ∥ₐ)
                  → (∀ {k} → reduce ψ (η k) ≈ θ k)
                  → ∀ {xs : Vec (Expr ((Σ Θ) ⦉ m ⦊)) arity}
                  → Pointwise _≈_ (map (reduce ψ) (subst-args ∥ M [ n ] ∥ₐ η xs))
                                  (subst-args ∥ M ∥ₐ θ xs)
    factor-args θ η ψ p {[]}     = []
    factor-args θ η ψ p {x ∷ xs} =
      factor θ η ψ p {x = x} ∷ factor-args θ η ψ p {xs = xs}

    factor : ∀ {m}
             → (θ : Environment m ∥ M ∥ₐ)
             → (η : Environment m ∥ M [ n ] ∥ₐ)
             → (ψ : Environment n ∥ M ∥ₐ)
             → (∀ {k} → reduce ψ (η k) ≈ θ k)
             → reduceₕ ψ ∘ₕ (substₕ (M [ n ]) η) ≡ₕ substₕ M θ
    factor θ η ψ p {term₂ k} = p
    factor θ η ψ p {term₁ f} = sym (∥ reduceₕ ψ ∥ₕ-hom f [])
    factor θ η ψ p {term f (x ∷ xs)}  = begin
        reduce ψ ((M [ n ] ⟦ f ⟧) (subst-args ∥ M [ n ] ∥ₐ η (x ∷ xs)))
      ≈⟨ sym (∥ reduceₕ ψ ∥ₕ-hom f (subst-args ∥ M [ n ] ∥ₐ η (x ∷ xs))) ⟩
        (M ⟦ f ⟧) (map (reduce ψ) (subst-args ∥ M [ n ] ∥ₐ η (x ∷ xs)))
      ≈⟨ (M ⟦⟧-cong) f (factor-args θ η ψ p {xs = x ∷ xs}) ⟩
        (M ⟦ f ⟧) (subst-args ∥ M ∥ₐ θ (x ∷ xs))
      ∎

  fundamental : ∀ {x y : ∥ M ∥} {x' y' : ∥ M [ n ] ∥}
                → (θ : Environment n ∥ M ∥ₐ)
                → reduce θ x' ≈ x
                → reduce θ y' ≈ y
                → x' ≈ₓ y'
                → x ≈ y
  fundamental θ p q x'≈ₓy' = trans (trans (sym p) (∥ reduceₕ θ ∥ₕ-cong x'≈ₓy')) q
