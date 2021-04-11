{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory.Base

module Fragment.Extensions.Combinators {Θ : Theory} where

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Combinators
open import Fragment.Algebra.Algebra using (∥_∥/≈-isAlgebra)
open import Fragment.Algebra.Homomorphism (Σ Θ)
open import Fragment.Algebra.FreeAlgebra
open import Fragment.Algebra.TermAlgebra
open import Fragment.Algebra.Algebra
  using (Algebra; IsAlgebra; algebra; Interpretation; Congruence)

open import Fragment.Equational.Theory.Combinators
open import Fragment.Equational.Satisfaction
open import Fragment.Equational.Model hiding (∥_∥/≈-isAlgebra)
open import Fragment.Equational.FreeExtension
open import Fragment.Equational.Coproduct

open import Level using (Level; _⊔_)
open import Function using (_∘_)

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Fin using (zero; #_)
open import Data.Vec using ([]; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise; []; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_) renaming ([_] to ≡[_])
open import Relation.Nullary using (yes ; no)

private
  variable
    a ℓ : Level

module _
  (FX : FreeExtension Θ)
  (• : ops (Σ Θ) 2)
  where

  open FreeExtension FX

  forgetId : Model (AddId Θ •) {a} {ℓ} → Model Θ {a} {ℓ}
  forgetId M = record { ∥_∥/≈   = ∥ M ∥/≈
                      ; isModel = forgetId-isModel
                      }
    where forgetId-models : Models Θ (forget ∥ M ∥ₐ)
          forgetId-models eq {θ} =
            forget-⊨ {A = ∥ M ∥ₐ} {eq = Θ ⟦ eq ⟧ₑ}
              (∥ M ∥ₐ-models (inherited eq)) {θ}
          forgetId-isModel : IsModel Θ ∥ M ∥/≈
          forgetId-isModel =
            record { isAlgebra = ∥ forget ∥ M ∥ₐ ∥/≈-isAlgebra
                   ; models    = forgetId-models
                   }

  module _ (M : Model (AddId Θ •) {a} {ℓ}) (n : ℕ) where

    e : ∥ forgetId M ∥
    e = (M ⟦ inj₂ zero ⟧) []

    private
      ⟦_⟧ₓ = λ {arity} → _⟦_⟧ ((forgetId M) [ n ]) {arity = arity}
      ⟦⟧ₓ-cong = λ {arity} → _⟦⟧-cong ((forgetId M) [ n ]) {arity = arity}

    open IsCoproduct ((forgetId M) [ n ]-isFrex)

    open module X = Setoid ∥ (forgetId M) [ n ] ∥/≈ renaming (_≈_ to _≈ₓ_)
    open module M = Setoid ∥ M ∥/≈ renaming (_≈_ to _≈ₘ_)
    open Signature (Σ (AddId Θ •)) using (_≟_)

{-
    id-⟦_⟧ : Interpretation (Σ (AddId Θ •)) ≈-setoid
    id-⟦ inj₁ f ⟧ []      = take (⟦ f ⟧ₓ [])
    id-⟦ inj₂ zero ⟧ []   = id
    id-⟦ f ⟧ (x ∷ y ∷ []) with _≟_ {n = 2} f •
    ...                  | yes _ = x ++ y
    ...                  | no _  = take (⟦ f ⟧ₓ (map restore (x ∷ y ∷ [])))
    id-⟦ f ⟧ (x ∷ xs)     = take (⟦ f ⟧ₓ (map restore (x ∷ xs)))

    id-⟦⟧-cong : Congruence (Σ (AddId Θ •)) ≈-setoid id-⟦_⟧
    id-⟦⟧-cong (inj₁ f) []        = take (⟦⟧ₓ-cong f [])
    id-⟦⟧-cong (inj₂ zero) []     = id₁
    id-⟦⟧-cong f (p ∷ q ∷ [])
      with _≟_ {n = 2} f •
    ...  | yes _ = ++-cong p q
    ...  | no _  = take (⟦⟧ₓ-cong f (restore-cong p ∷ restore-cong q ∷ []))
    id-⟦⟧-cong f (p ∷ [])         = take (⟦⟧ₓ-cong f (restore-cong p ∷ []))
    id-⟦⟧-cong f (p ∷ q ∷ r ∷ ps) =
      take (⟦⟧ₓ-cong f (PW.map⁺ restore-cong (p ∷ q ∷ r ∷ ps)))
-}

{-
    id-isAlgebra : IsAlgebra (Σ (AddId Θ •)) ≈ᵢ-setoid
    id-isAlgebra = record { ⟦_⟧     = id-⟦_⟧
                          ; ⟦⟧-cong = id-⟦⟧-cong
                          }

    id-⟦•⟧≡++ : ∀ {f x y} → (f ≡ •) → id-⟦ f ⟧ (x ∷ y ∷ []) ≡ x ++ y
    id-⟦•⟧≡++ {f} f≡• with _≟_ {n = 2} f •
    ...          | yes _ = PE.refl
    ...          | no ¬p  = ⊥-elim (¬p f≡•)
-}

{-
  AddIdFrex : FreeExtension (AddId Θ •)
  AddIdFrex = record { _[_]        = id-model
                     ; _[_]-isFrex = id-model-isFrex
                     }
-}
