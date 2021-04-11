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
open import Fragment.Equational.Model hiding (∥_∥/≈-isAlgebra)
open import Fragment.Equational.FreeExtension
open import Fragment.Equational.Coproduct

open import Level using (Level; _⊔_)

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Fin using (zero; #_)
open import Data.Vec using ([]; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise; []; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
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

    open IsCoproduct ((forgetId M) [ n ]-isFrex)

    open module X = Setoid ∥ (forgetId M) [ n ] ∥/≈ using (_≈_)
    open module M = Setoid ∥ M ∥/≈ renaming (_≈_ to _≈ₘ_)
    open Signature (Σ (AddId Θ •)) using (_≟_)

    data Id : Set a where
      id   : Id
      take : ∥ (forgetId M) [ n ] ∥ → Id

    infix 6 _≈ᵢ_

    data _≈ᵢ_ : Id → Id → Set (a ⊔ ℓ) where
      ≈-id   : id ≈ᵢ id
      ≈-take : ∀ {x y} → x ≈ y → take x ≈ᵢ take y

    ≈ᵢ-refl : ∀ {x} → x ≈ᵢ x
    ≈ᵢ-refl {x = id}     = ≈-id
    ≈ᵢ-refl {x = take x} = ≈-take (X.refl)

    ≈ᵢ-sym : ∀ {x y} → x ≈ᵢ y → y ≈ᵢ x
    ≈ᵢ-sym ≈-id       = ≈-id
    ≈ᵢ-sym (≈-take p) = ≈-take (X.sym p)

    ≈ᵢ-trans : ∀ {x y z} → x ≈ᵢ y → y ≈ᵢ z → x ≈ᵢ z
    ≈ᵢ-trans ≈-id ≈-id             = ≈-id
    ≈ᵢ-trans (≈-take p) (≈-take q) = ≈-take (X.trans p q)

    ≈ᵢ-isEquivalence : IsEquivalence _≈ᵢ_
    ≈ᵢ-isEquivalence = record { refl  = ≈ᵢ-refl
                              ; sym   = ≈ᵢ-sym
                              ; trans = ≈ᵢ-trans
                              }

    ≈ᵢ-setoid : Setoid a (a ⊔ ℓ)
    ≈ᵢ-setoid = record { Carrier       = Id
                       ; _≈_           = _≈ᵢ_
                       ; isEquivalence = ≈ᵢ-isEquivalence
                       }

    open module S = Setoid ≈ᵢ-setoid hiding (_≈_)

    restore : ∀ (x : Id) → ∥ (forgetId M) [ n ] ∥
    restore id       = ∥ inl ∥ₕ e
    restore (take x) = x

    restore-cong : ∀ {x y} → x ≈ᵢ y → restore x ≈ restore y
    restore-cong ≈-id       = X.refl
    restore-cong (≈-take p) = p

    private
      ⟦_⟧ₓ = λ {arity} → _⟦_⟧ ((forgetId M) [ n ]) {arity = arity}
      ⟦⟧ₓ-cong = λ {arity} → _⟦⟧-cong ((forgetId M) [ n ]) {arity = arity}

    _++_ : Id → Id → Id
    id     ++ x      = x
    take x ++ id     = take x
    take x ++ take y = take (⟦ • ⟧ₓ (x ∷ y ∷ []))

    ++-idₗ : ∀ (x : Id) → id ++ x ≈ᵢ x
    ++-idₗ id       = ≈-id
    ++-idₗ (take x) = ≈-take X.refl

    ++-idᵣ : ∀ (x : Id) → x ++ id ≈ᵢ x
    ++-idᵣ id       = ≈-id
    ++-idᵣ (take x) = ≈-take X.refl

    ++-cong : ∀ {x y z w} → x ≈ᵢ y → z ≈ᵢ w → x ++ z ≈ᵢ y ++ w
    ++-cong ≈-id q                = q
    ++-cong (≈-take p) ≈-id       = ≈-take p
    ++-cong (≈-take p) (≈-take q) = ≈-take (⟦⟧ₓ-cong • (p ∷ q ∷ []))

    id-⟦_⟧ : Interpretation (Σ (AddId Θ •)) ≈ᵢ-setoid
    id-⟦ inj₁ f ⟧ []      = take (⟦ f ⟧ₓ [])
    id-⟦ inj₂ zero ⟧ []   = id
    id-⟦ f ⟧ (x ∷ y ∷ []) with _≟_ {n = 2} f •
    ...                  | yes _ = x ++ y
    ...                  | no _  = take (⟦ f ⟧ₓ (map restore (x ∷ y ∷ [])))
    id-⟦ f ⟧ (x ∷ xs)     = take (⟦ f ⟧ₓ (map restore (x ∷ xs)))

    id-⟦⟧-cong : Congruence (Σ (AddId Θ •)) ≈ᵢ-setoid id-⟦_⟧
    id-⟦⟧-cong (inj₁ f) []        = ≈-take (⟦⟧ₓ-cong f [])
    id-⟦⟧-cong (inj₂ zero) []     = ≈-id
    id-⟦⟧-cong f (p ∷ q ∷ [])
      with _≟_ {n = 2} f •
    ...  | yes _ = ++-cong p q
    ...  | no _  = ≈-take (⟦⟧ₓ-cong f (restore-cong p ∷ restore-cong q ∷ []))
    id-⟦⟧-cong f (p ∷ [])         = ≈-take (⟦⟧ₓ-cong f (restore-cong p ∷ []))
    id-⟦⟧-cong f (p ∷ q ∷ r ∷ ps) =
      ≈-take (⟦⟧ₓ-cong f (PW.map⁺ restore-cong (p ∷ q ∷ r ∷ ps)))

    id-isAlgebra : IsAlgebra (Σ (AddId Θ •)) ≈ᵢ-setoid
    id-isAlgebra = record { ⟦_⟧     = id-⟦_⟧
                          ; ⟦⟧-cong = id-⟦⟧-cong
                          }

    id-⟦•⟧≡++ : ∀ {f x y} → (f ≡ •) → id-⟦ f ⟧ (x ∷ y ∷ []) ≡ x ++ y
    id-⟦•⟧≡++ {f} f≡• with _≟_ {n = 2} f •
    ...          | yes _ = PE.refl
    ...          | no ¬p  = ⊥-elim (¬p f≡•)

    id-algebra : Algebra (Σ (AddId Θ •))
    id-algebra = algebra ≈ᵢ-setoid id-isAlgebra

    open import Relation.Binary.Reasoning.Setoid ≈ᵢ-setoid

    id-models : Models (AddId Θ •) id-algebra
    id-models idₗ {θ}            = begin
        id-⟦ • ⟧ (id ∷ (θ (# 0)) ∷ [])
      ≈⟨ S.reflexive (id-⟦•⟧≡++ PE.refl) ⟩
        id ++ (θ (# 0))
      ≈⟨ ++-idₗ (θ (# 0)) ⟩
        θ (# 0)
      ∎
    id-models idᵣ {θ}            = begin
        id-⟦ • ⟧ ((θ (# 0)) ∷ id ∷ [])
      ≈⟨ S.reflexive (id-⟦•⟧≡++ PE.refl) ⟩
        (θ (# 0)) ++ id
      ≈⟨ ++-idᵣ (θ (# 0)) ⟩
        θ (# 0)
      ∎
    id-models (inherited eq) {θ} = {!!}
      where lhs = proj₁ ((AddId Θ •) ⟦ inherited eq ⟧ₑ)
            rhs = proj₂ ((AddId Θ •) ⟦ inherited eq ⟧ₑ)

    id-isModel : IsModel (AddId Θ •) ≈ᵢ-setoid
    id-isModel = record { isAlgebra = id-isAlgebra
                        ; models    = id-models
                        }

    id-model : Model (AddId Θ •) {a} {a ⊔ ℓ}
    id-model = record { ∥_∥/≈   = ≈ᵢ-setoid
                      ; isModel = id-isModel
                      }

{-
  id-model-isFrex : IsFreeExtension (AddId Θ •) id-model
  id-model-isFrex M n =
    record { inl       = {!!}
           ; inr       = {!!}
           ; [_,_]     = {!!}
           ; commute₁  = {!!}
           ; commute₂  = {!!}
           ; universal = {!!}
           }
    where open IsCoproduct ((forgetId M) [ n ]-isFrex)

  AddIdFrex : FreeExtension (AddId Θ •)
  AddIdFrex = record { _[_]        = id-model
                     ; _[_]-isFrex = id-model-isFrex
                     }
-}
