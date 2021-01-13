{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism (Σ : Signature) where

open import Level using (_⊔_)
open import Data.Vec
open import Function
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open import Fragment.Algebra.Algebra

module _
  {a b ℓ₁ ℓ₂}
  {S : Setoid a ℓ₁}
  {T : Setoid b ℓ₂}
  (Sᴬ : IsAlgebra S Σ)
  (Tᴬ : IsAlgebra T Σ)
  where

  open Setoid S renaming (Carrier to A; _≈_ to _≈ₛ_)
  open Setoid T renaming (Carrier to B; _≈_ to _≈ₜ_)

  open IsAlgebra Sᴬ renaming (⟦_⟧ to S⟦_⟧)
  open IsAlgebra Tᴬ renaming (⟦_⟧ to T⟦_⟧)

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
  {a b ℓ₁ ℓ₂}
  {S : Setoid a ℓ₁}
  {T : Setoid b ℓ₂}
  (Sᴬ : IsAlgebra S Σ)
  (Tᴬ : IsAlgebra T Σ)
  where

  open Setoid T

  open import Relation.Binary.Definitions
    using (Reflexive; Transitive; Symmetric)
  open import Data.Vec.Relation.Binary.Equality.Setoid T

  _≈ₕ_ : Rel (Sᴬ →ₕ Tᴬ) (a ⊔ ℓ₂)
  fₕ ≈ₕ gₕ = ∀ {x} → (_→ₕ_.h fₕ) x ≈ (_→ₕ_.h gₕ) x

  ≈ₕ-refl : Reflexive _≈ₕ_
  ≈ₕ-refl = refl

  ≈ₕ-sym : Symmetric _≈ₕ_
  ≈ₕ-sym fₕ≈ₕgₕ = ?

  ≈ₕ-trans : Transitive _≈ₕ_
  ≈ₕ-trans = ?

  {-
  ≈ₕ-isEquivalence : IsEquivalence _≈ₕ_
  ≈ₕ-isEquivalence = record { refl  = ≈ₕ-refl
                            ; sym   = ≈ₕ-sym
                            ; trans = ≈ₕ-trans
                            }

  ≈ₕ-setoid : Setoid _ _
  ≈ₕ-setoid = record { Carrier       = Sᴬ →ₕ Tᴬ
                     ; _≈_           = _≈ₕ_
                     ; isEquivalence = ≈ₕ-isEquivalence
                     }
  -}

module _ {a ℓ} {S : Setoid a ℓ} (Sᴬ : IsAlgebra S Σ) where

  open Setoid S renaming (Carrier to A)
  open IsAlgebra Sᴬ

  open import Data.Vec.Properties using (map-id)
  open import Data.Vec.Relation.Binary.Equality.Setoid S
  open import Relation.Binary.Reasoning.Setoid S

  id-cong : Congruent _≈_ _≈_ id
  id-cong x≈y = x≈y

  id-hom : Homomorphic Sᴬ Sᴬ id
  id-hom {n} f xs = begin
      ⟦ f ⟧ (map id xs)
    ≈⟨ ⟦⟧-cong f $ IsEquivalence.reflexive (≋-isEquivalence n) (map-id xs) ⟩
      ⟦ f ⟧ (xs)
    ∎

  idₕ : Sᴬ →ₕ Sᴬ
  idₕ = record { h      = id
               ; h-cong = id-cong
               ; h-hom  = id-hom
               }

module _
  {a b c ℓ₁ ℓ₂ ℓ₃}
  {S : Setoid a ℓ₁}
  {T : Setoid b ℓ₂}
  {U : Setoid c ℓ₃}
  {Sᴬ : IsAlgebra S Σ}
  {Tᴬ : IsAlgebra T Σ}
  {Uᴬ : IsAlgebra U Σ}
  (hₕ : Tᴬ →ₕ Uᴬ)
  (gₕ : Sᴬ →ₕ Tᴬ)
  where

  open Setoid S renaming (Carrier to A; _≈_ to _≈ₛ_)
  open Setoid T renaming (Carrier to B; _≈_ to _≈ₜ_)
  open Setoid U renaming (Carrier to C; _≈_ to _≈ᵤ_; isEquivalence to ≈ᵤ-isEquivalence)

  open IsAlgebra Sᴬ renaming (⟦_⟧ to S⟦_⟧)
  open IsAlgebra Tᴬ renaming (⟦_⟧ to T⟦_⟧)
  open IsAlgebra Uᴬ renaming (⟦_⟧ to U⟦_⟧; ⟦⟧-cong to U⟦⟧-cong)

  open _→ₕ_ hₕ
  open _→ₕ_ gₕ renaming (h to g; h-cong to g-cong; h-hom to g-hom)

  open import Data.Vec.Properties using (map-∘)
  open import Data.Vec.Relation.Binary.Equality.Setoid U
  open import Relation.Binary.Reasoning.Setoid U
  open import Function.Construct.Composition using (congruent)

  ∘ₕ-cong : Congruent _≈ₛ_ _≈ᵤ_ (h ∘ g)
  ∘ₕ-cong = congruent _≈ₛ_ _≈ₜ_ _≈ᵤ_ g-cong h-cong

  ∘ₕ-hom : Homomorphic Sᴬ Uᴬ (h ∘ g)
  ∘ₕ-hom {n} f xs = begin
      U⟦ f ⟧ (map (h ∘ g) xs)
    ≈⟨ U⟦⟧-cong f $ IsEquivalence.reflexive (≋-isEquivalence n) (map-∘ h g xs) ⟩
      U⟦ f ⟧ (map h (map g xs))
    ≈⟨ h-hom f (map g xs) ⟩
      h (T⟦ f ⟧ (map g xs))
    ≈⟨ h-cong (g-hom f xs) ⟩
      h (g (S⟦ f ⟧ xs))
    ∎

  _∘ₕ_ : (Sᴬ →ₕ Uᴬ)
  _∘ₕ_ = record { h      = h ∘ g
                ; h-cong = ∘ₕ-cong
                ; h-hom  = ∘ₕ-hom
                }

module _
  {a b c d ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  {S : Setoid a ℓ₁}
  {T : Setoid b ℓ₂}
  {U : Setoid c ℓ₃}
  {V : Setoid d ℓ₄}
  {Sᴬ : IsAlgebra S Σ}
  {Tᴬ : IsAlgebra T Σ}
  {Uᴬ : IsAlgebra U Σ}
  {Vᴬ : IsAlgebra V Σ}
  (hₕ : Uᴬ →ₕ Vᴬ)
  (gₕ : Tᴬ →ₕ Uᴬ)
  (fₕ : Sᴬ →ₕ Tᴬ)
  where

  ∘ₕ-assoc : _≈ₕ_ Sᴬ Vᴬ ((hₕ ∘ₕ gₕ) ∘ₕ fₕ) (hₕ ∘ₕ (gₕ ∘ₕ fₕ))
  ∘ₕ-assoc = ?
