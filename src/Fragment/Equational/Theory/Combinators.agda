{-# OPTIONS --without-K --exact-split --safe #-}

open import Fragment.Equational.Theory.Base

module Fragment.Equational.Theory.Combinators (Θ : Theory) where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Properties
open import Fragment.Equational.Model
  using (Model; IsModel; Models)
open import Fragment.Equational.Model.Satisfaction

open import Level using (Level)
open import Function using (_∘_)

open import Data.Nat using (ℕ)

private
  variable
    a ℓ : Level

{-
forgetₒ' : ∀ {O} → Model (Θ ⦅ O ⦆ₒ) {a} {ℓ} → Model Θ {a} {ℓ}
forgetₒ' {O = O} A =
  record { ∥_∥/≈   = ∥ A ∥/≈
         ; isModel = forget-isModel
         }
  where open import Fragment.Equational.Model (Θ ⦅ O ⦆ₒ)
          using (∥_∥/≈; ∥_∥ₐ; ∥_∥ₐ-models)
        open import Fragment.Algebra.Algebra (Σ Θ)
          using (∥_∥/≈-isAlgebra)

        forget-⊨ : ∀ {θ eq} → ∥ A ∥ₐ ⊨⟨ θ ⟩ ((Θ ⦅ O ⦆ₒ) ⟦ {!oldₑ!} ⟧ₑ)
                            → forgetₒ ∥ A ∥ₐ ⊨⟨ θ ⟩ (Θ ⟦ eq ⟧ₑ)
        forget-⊨ = {!!}

        forget-models : Models Θ (forgetₒ ∥ A ∥ₐ)
        forget-models eq θ = {!!}

        forget-isModel : IsModel Θ ∥ A ∥/≈
        forget-isModel =
          record { isAlgebra = ∥ (forgetₒ ∥ A ∥ₐ) ∥/≈-isAlgebra
                 ; models    = forget-models
                 }

forgetₑ : ∀ {O E}
          → {X : ∀ {n} → E n → Eq ((Σ Θ) ⦅ O ⦆) n}
          → Model (Θ ⦅ O ∣ E / X ⦆) {a} {ℓ}
          → Model Θ {a} {ℓ}
forgetₑ {O = O} {E} {X} A =
  record { ∥_∥/≈   = {!!}
         ; isModel = {!!}
         }
-}

data HomOp : ℕ → Set where
  h : HomOp 1

data HomEq : ℕ → Set where
  hom : ∀ {n} → ops (Σ Θ) n → HomEq n

AddHom : Theory
AddHom = Θ ⦅ HomOp ∣ HomEq / hom' ⦆
  where import Fragment.Equational.Theory.Laws ((Σ Θ) ⦅ HomOp ⦆) as L

        hom' : ∀ {arity} → HomEq arity → Eq ((Σ Θ) ⦅ HomOp ⦆) arity
        hom' (hom f) = L.hom (newₒ h) (oldₒ f)

data IdOp : ℕ → Set where
  α : IdOp 0

data IdEq : ℕ → Set where
  idₗ : IdEq 1
  idᵣ : IdEq 1

AddId : ops (Σ Θ) 2 → Theory
AddId • = Θ ⦅ IdOp ∣ IdEq / id ⦆
  where import Fragment.Equational.Theory.Laws ((Σ Θ) ⦅ IdOp ⦆) as L

        id : ∀ {arity} → IdEq arity → Eq ((Σ Θ) ⦅ IdOp ⦆) arity
        id idₗ = L.idₗ (newₒ α) (oldₒ •)
        id idᵣ = L.idᵣ (newₒ α) (oldₒ •)

data AnOp : ℕ → Set where
  ω : AnOp 0

data AnEq : ℕ → Set where
  anₗ : AnEq 1
  anᵣ : AnEq 1

AddAn : ops (Σ Θ) 2 → Theory
AddAn • = Θ ⦅ AnOp ∣ AnEq / an ⦆
  where import Fragment.Equational.Theory.Laws ((Σ Θ) ⦅ AnOp ⦆) as L

        an : ∀ {arity} → AnEq arity → Eq ((Σ Θ) ⦅ AnOp ⦆) arity
        an anₗ = L.anₗ (newₒ ω) (oldₒ •)
        an anᵣ = L.anᵣ (newₒ ω) (oldₒ •)
