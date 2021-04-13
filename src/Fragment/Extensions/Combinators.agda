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

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (zero; #_)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise; []; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)

open import Relation.Nullary using (yes ; no; Dec)
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

    private
      ⟦_⟧ₓ = λ {arity} → _⟦_⟧ ((forgetId M) [ n ]) {arity = arity}
      ⟦⟧ₓ-cong = λ {arity} → _⟦⟧-cong ((forgetId M) [ n ]) {arity = arity}

    open IsCoproduct ((forgetId M) [ n ]-isFrex)

    open module X = Setoid ∥ (forgetId M) [ n ] ∥/≈ renaming (_≈_ to _≈ₓ_)
    open module M = Setoid ∥ M ∥/≈ renaming (_≈_ to _≈ₘ_)
    open Signature (Σ (AddId Θ •)) using (_≟_)

    e : ∥ forgetId M ∥
    e = (M ⟦ inj₂ zero ⟧) []

    module _ (_≟e : ∀ x → Dec (x ≈ₓ ∥ inl ∥ₕ e)) where

      data Id : Set a where
        id      : Id
        inherit : ∥ (forgetId M) [ n ] ∥ → Id

      infix 6 _≈_

      data _≈_ : Id → Id → Set (a ⊔ ℓ) where
        id-refl : id ≈ id
        ≈ₓ-pres : ∀ {x y} → x ≈ₓ y → inherit x ≈ inherit y

      ≈-refl : ∀ {x} → x ≈ x
      ≈-refl {x = id}        = id-refl
      ≈-refl {x = inherit _} = ≈ₓ-pres (X.refl)

      ≈-sym : ∀ {x y} → x ≈ y → y ≈ x
      ≈-sym id-refl     = id-refl
      ≈-sym (≈ₓ-pres p) = ≈ₓ-pres (X.sym p)

      ≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
      ≈-trans id-refl id-refl         = id-refl
      ≈-trans (≈ₓ-pres p) (≈ₓ-pres q) = ≈ₓ-pres (X.trans p q)

      ≈-isEquivalence : IsEquivalence _≈_
      ≈-isEquivalence = record { refl  = ≈-refl
                               ; sym   = ≈-sym
                               ; trans = ≈-trans
                               }

      ≈-setoid : Setoid a (a ⊔ ℓ)
      ≈-setoid = record { Carrier       = Id
                        ; _≈_           = _≈_
                        ; isEquivalence = ≈-isEquivalence
                        }

      data Normal : Id → Set (a ⊔ ℓ) where
        id      : Normal id
        inherit : ∀ {x} → (x ≈ₓ ∥ inl ∥ₕ e → ⊥) → Normal (inherit x)

      normalise : Id → Id
      normalise id = id
      normalise (inherit x)
        with x ≟e
      ... | yes _ = id
      ... | no _  = inherit x

      normalise-cong : ∀ {x y} → x ≈ₓ y
                       → normalise (inherit x) ≈ normalise (inherit y)
      normalise-cong {x} {y} p
        with x ≟e  | y ≟e
      ...  | yes _ | yes _ = id-refl
      ...  | yes q | no ¬q = ⊥-elim (¬q (X.trans (X.sym p) q))
      ...  | no ¬q | yes q = ⊥-elim (¬q (X.trans p q))
      ...  | no _  | no _  = ≈ₓ-pres p

      normalise-reduction : ∀ {x} → Normal (normalise x)
      normalise-reduction {x = id} = id
      normalise-reduction {x = inherit x}
        with x ≟e
      ...  | yes _ = id
      ...  | no ¬e = inherit ¬e

      _++-raw_ : Id → Id → Id
      id        ++-raw y         = y
      inherit x ++-raw id        = inherit x
      inherit x ++-raw inherit y =
        normalise (inherit (⟦ • ⟧ₓ (x ∷ y ∷ [])))

      _++ₙ_ : ∀ {x y} → Normal x → Normal y → Normal (x ++-raw y)
      id          ++ₙ id          = id
      id          ++ₙ (inherit q) = inherit q
      (inherit p) ++ₙ id          = inherit p
      (inherit p) ++ₙ (inherit q) = normalise-reduction

      NormalId : Set (a ⊔ ℓ)
      NormalId = Σ[ x ∈ Id ] (Normal x)

      pattern idₙ = (id , id)

      take : ∥ (forgetId M) [ n ] ∥ → NormalId
      take x = normalise (inherit x) , normalise-reduction

      drop : NormalId → ∥ (forgetId M) [ n ] ∥
      drop idₙ             = ∥ inl ∥ₕ e
      drop (inherit x , _) = x

      infix 6 _≈ₙ_

      _≈ₙ_ : NormalId → NormalId → Set (a ⊔ ℓ)
      (x , _) ≈ₙ (y , _) = x ≈ y

      ≈ₙ-isEquivalence : IsEquivalence _≈ₙ_
      ≈ₙ-isEquivalence = record { refl  = ≈-refl
                                ; sym   = ≈-sym
                                ; trans = ≈-trans
                                }

      ≈ₙ-setoid : Setoid (a ⊔ ℓ) (a ⊔ ℓ)
      ≈ₙ-setoid = record { Carrier       = NormalId
                         ; _≈_           = _≈ₙ_
                         ; isEquivalence = ≈ₙ-isEquivalence
                         }

      open module N = Setoid ≈ₙ-setoid hiding (_≈_)

      _++_ : NormalId → NormalId → NormalId
      (x , p) ++ (y , q) = x ++-raw y , p ++ₙ q

      ++-raw-idₗ : ∀ x → id ++-raw x ≈ x
      ++-raw-idₗ id          = ≈-refl
      ++-raw-idₗ (inherit _) = ≈-refl

      ++-raw-idᵣ : ∀ x → x ++-raw id ≈ x
      ++-raw-idᵣ id          = ≈-refl
      ++-raw-idᵣ (inherit _) = ≈-refl

      ++-raw-cong : ∀ {x y z w} → x ≈ y → z ≈ w
                    → x ++-raw z ≈ y ++-raw w
      ++-raw-cong id-refl     q           = q
      ++-raw-cong (≈ₓ-pres p) id-refl     = ≈ₓ-pres p
      ++-raw-cong (≈ₓ-pres p) (≈ₓ-pres q) =
        normalise-cong (⟦⟧ₓ-cong • (p ∷ q ∷ []))

      ++-idₗ : ∀ x → idₙ ++ x ≈ₙ x
      ++-idₗ (x , _) = ++-raw-idₗ x

      ++-idᵣ : ∀ x → x ++ idₙ ≈ₙ x
      ++-idᵣ (x , _) = ++-raw-idᵣ x

      ++-cong : ∀ {x y z w} → x ≈ₙ y → z ≈ₙ w
                → x ++ z ≈ₙ y ++ w
      ++-cong = ++-raw-cong

      drop-cong : ∀ {x y} → x ≈ₙ y → drop x ≈ₓ drop y
      drop-cong {idₙ} {idₙ} id-refl                         = X.refl
      drop-cong {inherit x , p} {inherit y , q} (≈ₓ-pres r) = r

      id-⟦_⟧ : Interpretation (Σ (AddId Θ •)) ≈ₙ-setoid
      id-⟦ inj₁ f ⟧ []    = take (⟦ f ⟧ₓ [])
      id-⟦ inj₂ zero ⟧ [] = idₙ
      id-⟦ f ⟧ (x ∷ y ∷ [])
        with _≟_ {n = 2} f •
      ...  | yes _ = x ++ y
      ...  | no _  = take (⟦ f ⟧ₓ (drop x ∷ drop y ∷ []))
      id-⟦ f ⟧ (x ∷ xs) = take (⟦ f ⟧ₓ (map drop (x ∷ xs)))

      id-⟦⟧-cong : Congruence (Σ (AddId Θ •)) ≈ₙ-setoid id-⟦_⟧
      id-⟦⟧-cong (inj₁ f) []    = normalise-cong X.refl
      id-⟦⟧-cong (inj₂ zero) [] = id-refl
      id-⟦⟧-cong f (p ∷ q ∷ [])
        with _≟_ {n = 2} f •
      ...  | yes _ = ++-raw-cong p q
      ...  | no _  = normalise-cong (⟦⟧ₓ-cong f (drop-cong p ∷ drop-cong q ∷ []))
      id-⟦⟧-cong f (p ∷ [])         = normalise-cong (⟦⟧ₓ-cong f (drop-cong p ∷ []))
      id-⟦⟧-cong f (p ∷ q ∷ r ∷ ps) =
        normalise-cong (⟦⟧ₓ-cong f (PW.map⁺ drop-cong (p ∷ q ∷ r ∷ ps)))

      id-isAlgebra : IsAlgebra (Σ (AddId Θ •)) ≈ₙ-setoid
      id-isAlgebra = record { ⟦_⟧     = id-⟦_⟧
                            ; ⟦⟧-cong = id-⟦⟧-cong
                            }

      id-algebra = algebra ≈ₙ-setoid id-isAlgebra

      id-⟦•⟧≡++ : ∀ {f x y} → (f ≡ •) → id-⟦ f ⟧ (x ∷ y ∷ []) ≡ x ++ y
      id-⟦•⟧≡++ {f} f≡• with _≟_ {n = 2} f •
      ...          | yes _ = PE.refl
      ...          | no ¬p  = ⊥-elim (¬p f≡•)

      open import Relation.Binary.Reasoning.Setoid ≈ₙ-setoid

      id-models : Models (AddId Θ •) id-algebra
      id-models idₗ {θ} = begin
          id-⟦ • ⟧ (idₙ ∷ (θ (# 0)) ∷ [])
        ≡⟨ id-⟦•⟧≡++ PE.refl ⟩
          idₙ ++ (θ (# 0))
        ≈⟨ ++-idₗ (θ (# 0)) ⟩
          θ (# 0)
        ∎
      id-models idᵣ {θ} = begin
          id-⟦ • ⟧ (θ (# 0) ∷ idₙ ∷ [])
        ≡⟨ id-⟦•⟧≡++ PE.refl ⟩
          (θ (# 0)) ++ idₙ
        ≈⟨ ++-idᵣ (θ (# 0)) ⟩
          θ (# 0)
        ∎
      id-models (inherited eq) {θ} = begin
          subst _ id-algebra θ (extend-expr (proj₁ (Θ ⟦ eq ⟧ₑ)))
        ≈⟨ {!!} ⟩
          take (subst _ ∥ (forgetId M) [ n ] ∥ₐ (drop ∘ θ) (proj₁ (Θ ⟦ eq ⟧ₑ)))
        ≈⟨ normalise-cong (∥ forgetId M [ n ] ∥ₐ-models eq) ⟩
          take (subst _ ∥ (forgetId M) [ n ] ∥ₐ (drop ∘ θ) (proj₂ (Θ ⟦ eq ⟧ₑ)))
        ≈⟨ {!!} ⟩
          subst _ id-algebra θ (extend-expr (proj₂ (Θ ⟦ eq ⟧ₑ)))
        ∎

{-
  AddIdFrex : FreeExtension (AddId Θ •)
  AddIdFrex = record { _[_]        = id-model
                     ; _[_]-isFrex = id-model-isFrex
                     }
-}
