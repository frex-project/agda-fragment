{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism (Σ : Signature) where

open import Level using (Level; _⊔_)
open import Data.Vec
open import Function using (_∘_; id; _$_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Fragment.Algebra.Algebra

private
  variable
    a b c d ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

module _
  (S : Algebra Σ {a} {ℓ₁})
  (T : Algebra Σ {b} {ℓ₂})
  where

  open Algebra S renaming (Carrier to A; _≈_ to _≈ₛ_; ⟦_⟧ to S⟦_⟧)
  open Algebra T renaming (Carrier to B; _≈_ to _≈ₜ_; ⟦_⟧ to T⟦_⟧)

  open import Function.Definitions using (Congruent) public

  Homomorphic : (A → B) → Set (a ⊔ ℓ₂)
  Homomorphic h = ∀ {arity} → (f : ops Σ arity)
                  → (xs : Vec A arity)
                  → T⟦ f ⟧ (map h xs) ≈ₜ h (S⟦ f ⟧ xs)

  record _→ₕ_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      h      : A → B
      h-cong : Congruent _≈ₛ_ _≈ₜ_ h
      h-hom  : Homomorphic h

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  (F : S →ₕ T)
  where

  open Algebra S renaming (Carrier to A)
  open Algebra T renaming (Carrier to B)

  open _→ₕ_ F renaming (h to f)

  applyₕ : A → B
  applyₕ x = f x

module Equivalence
  (S : Algebra Σ {a} {ℓ₁})
  (T : Algebra Σ {b} {ℓ₂})
  where

  open Algebra T

  infix 4 _≈ₕ_

  _≈ₕ_ : Rel (S →ₕ T) (a ⊔ ℓ₂)
  F ≈ₕ G = ∀ {x} → applyₕ F x ≈ applyₕ G x

  open import Relation.Binary.Definitions
    using (Reflexive; Transitive; Symmetric)

  ≈ₕ-refl : Reflexive _≈ₕ_
  ≈ₕ-refl = refl

  ≈ₕ-sym : Symmetric _≈ₕ_
  ≈ₕ-sym F≈ₕG {x} = sym (F≈ₕG {x})

  ≈ₕ-trans : Transitive _≈ₕ_
  ≈ₕ-trans F≈ₕG G≈ₕH {x} = trans (F≈ₕG {x}) (G≈ₕH {x})

{-
  ≈ₕ-isEquivalence : IsEquivalence _≈ₕ_
  ≈ₕ-isEquivalence = record { refl  = ≈ₕ-refl
                            ; sym   = ≈ₕ-sym
                            ; trans = ≈ₕ-trans
                            }

  ≈ₕ-setoid : Setoid _ _
  ≈ₕ-setoid = record { Carrier       = S →ₕ T
                     ; _≈_           = _≈ₕ_
                     ; isEquivalence = ≈ₕ-isEquivalence
                     }
-}

module _ (S : Algebra Σ {a} {ℓ₁}) where

  open Algebra S

  open import Data.Vec.Properties using (map-id)
  open import Data.Vec.Relation.Binary.Equality.Setoid Carrierₛ

  id-cong : Congruent _≈_ _≈_ id
  id-cong x≈y = x≈y

  id-hom : Homomorphic S S id
  id-hom {n} f xs =
    ⟦⟧-cong f $ IsEquivalence.reflexive (≋-isEquivalence n) (map-id xs)

  idₕ : S →ₕ S
  idₕ = record { h      = id
               ; h-cong = id-cong
               ; h-hom  = id-hom
               }

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  {U : Algebra Σ {c} {ℓ₃}}
  (H : T →ₕ U)
  (G : S →ₕ T)
  where

  open Algebra S renaming (Carrier to A; _≈_ to _≈ₛ_; ⟦_⟧ to S⟦_⟧)
  open Algebra T renaming (Carrier to B; _≈_ to _≈ₜ_; ⟦_⟧ to T⟦_⟧)
  open Algebra U
    renaming ( Carrier       to C
             ; _≈_           to _≈ᵤ_
             ; Carrierₛ      to Cₛ
             ; isEquivalence to ≈ᵤ-isEquivalence
             ; ⟦_⟧           to U⟦_⟧
             ; ⟦⟧-cong       to U⟦⟧-cong
             )

  open _→ₕ_ H
  open _→ₕ_ G renaming (h to g; h-cong to g-cong; h-hom to g-hom)

  open import Data.Vec.Properties using (map-∘)
  open import Data.Vec.Relation.Binary.Equality.Setoid Cₛ
  open import Relation.Binary.Reasoning.Setoid Cₛ
  open import Function.Construct.Composition using (congruent)

  ∘ₕ-cong : Congruent _≈ₛ_ _≈ᵤ_ (h ∘ g)
  ∘ₕ-cong = congruent _≈ₛ_ _≈ₜ_ _≈ᵤ_ g-cong h-cong

  ∘ₕ-hom : Homomorphic S U (h ∘ g)
  ∘ₕ-hom {n} f xs = begin
      U⟦ f ⟧ (map (h ∘ g) xs)
    ≈⟨ U⟦⟧-cong f $ IsEquivalence.reflexive (≋-isEquivalence n) (map-∘ h g xs) ⟩
      U⟦ f ⟧ (map h (map g xs))
    ≈⟨ h-hom f (map g xs) ⟩
      h (T⟦ f ⟧ (map g xs))
    ≈⟨ h-cong (g-hom f xs) ⟩
      h (g (S⟦ f ⟧ xs))
    ∎

  infixr 9 _∘ₕ_

  _∘ₕ_ : (S →ₕ U)
  _∘ₕ_ = record { h      = h ∘ g
                ; h-cong = ∘ₕ-cong
                ; h-hom  = ∘ₕ-hom
                }

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  (H : S →ₕ T)
  where

  open Algebra T
  open Equivalence S T

  idₕ-unitˡ : idₕ T ∘ₕ H ≈ₕ H
  idₕ-unitˡ {x} = refl

  idₕ-unitʳ : H ∘ₕ idₕ S ≈ₕ H
  idₕ-unitʳ {x} = refl

module _
  {S : Algebra Σ {a} {ℓ₁}}
  {T : Algebra Σ {b} {ℓ₂}}
  {U : Algebra Σ {c} {ℓ₃}}
  {V : Algebra Σ {d} {ℓ₄}}
  (H : U →ₕ V)
  (G : T →ₕ U)
  (F : S →ₕ T)
  where

  open Algebra V
  open Equivalence S V

  ∘ₕ-assoc : (H ∘ₕ G) ∘ₕ F ≈ₕ H ∘ₕ (G ∘ₕ F)
  ∘ₕ-assoc {x} = refl
