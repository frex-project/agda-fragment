{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Blackstone where

open import Level using (Level; _⊔_)
open import Function using (id; _∘_)

open import Data.Vec using (Vec; map; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)


private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _ (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) where

  open import Function using (Congruent)
  open Setoid S renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid T renaming (Carrier to B; _≈_ to _≈₂_)

  record _→ₛ_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ∥_∥ₛ      : A → B
      ∥_∥ₛ-cong : Congruent _≈₁_ _≈₂_ ∥_∥ₛ

  open _→ₛ_ public

lift : ∀ {A : Set a} {B : Setoid b ℓ₂}
       → (A → Setoid.Carrier B)
       → (PE.setoid A →ₛ B)
lift {B = B} f = record { ∥_∥ₛ = f
                        ; ∥_∥ₛ-cong = reflexive ∘ (PE.cong f)
                        }
     where open Setoid B

module _ (Σ : Signature) where

  open import Fragment.Algebra.Algebra Σ
  open import Fragment.Algebra.Homomorphism Σ

  ∥_∥ₕₛ : ∀ {A : Algebra {a} {ℓ₁}} {B : Algebra {b} {ℓ₂}}
          → A →ₕ B → ∥ A ∥/≈ →ₛ ∥ B ∥/≈
  ∥_∥ₕₛ f = record { ∥_∥ₛ = ∥ f ∥ₕ ; ∥_∥ₛ-cong = ∥ f ∥ₕ-cong }

  module _ {S : Setoid a ℓ₁} where

    open Setoid S renaming (Carrier to A)

    idₛ : S →ₛ S
    idₛ = record { ∥_∥ₛ      = id
                 ; ∥_∥ₛ-cong = id
                 }
  module _
    {S : Setoid a ℓ₁}
    {T : Setoid b ℓ₂}
    {U : Setoid c ℓ₃}
    where

    open Setoid S renaming (Carrier to A; _≈_ to _≈₁_)
    open Setoid T renaming (Carrier to B; _≈_ to _≈₂_)
    open Setoid U renaming (Carrier to C; _≈_ to _≈₃_)

    _∘ₛ_ : T →ₛ U → S →ₛ T → S →ₛ U
    g ∘ₛ f = record { ∥_∥ₛ      = ∥ g ∥ₛ ∘ ∥ f ∥ₛ
                    ; ∥_∥ₛ-cong = ∥ g ∥ₛ-cong ∘ ∥ f ∥ₛ-cong
                    }

  module _ (A : Set a) where

    data Term : Set a where
      atom : A → Term
      term : ∀ {arity} → (f : ops Σ arity) → Vec Term arity → Term

  mutual
    eval-args : ∀ {n} (A : Algebra {a} {ℓ₁})
              → Vec (Term ∥ A ∥) n → Vec ∥ A ∥ n
    eval-args A []       = []
    eval-args A (x ∷ xs) = eval A x ∷ eval-args A xs

    eval : (A : Algebra {a} {ℓ₁}) → Term ∥ A ∥ → ∥ A ∥
    eval _ (atom x)    = x
    eval A (term f xs) = (A ⟦ f ⟧) (eval-args A xs)

  mutual
    bind-args : ∀ {n} {A : Set a} {B : Set b}
                → (A → Term B)
                → Vec (Term A) n → Vec (Term B) n
    bind-args f []       = []
    bind-args f (x ∷ xs) = bind f x ∷ bind-args f xs

    bind : ∀ {A : Set a} {B : Set b}
           → (A → Term B) → Term A → Term B
    bind f (atom x)     = f x
    bind f (term op xs) = term op (bind-args f xs)

  module _ (S : Setoid a ℓ₁) where

    open Setoid S renaming (Carrier to A)

    data _≈ₜ_ : Term A → Term A → Set (a ⊔ ℓ₁) where
      atom : ∀ {x y} → x ≈ y → atom x ≈ₜ atom y
      term : ∀ {arity xs ys} {f : ops Σ arity}
             → Pointwise _≈ₜ_ xs ys
             → term f xs ≈ₜ term f ys

    mutual
      ≈ₜ-refl-args : ∀ {n} {xs : Vec _ n} → Pointwise _≈ₜ_ xs xs
      ≈ₜ-refl-args {xs = []}     = []
      ≈ₜ-refl-args {xs = x ∷ xs} = ≈ₜ-refl ∷ ≈ₜ-refl-args

      ≈ₜ-refl : ∀ {x} → x ≈ₜ x
      ≈ₜ-refl {atom _}   = atom refl
      ≈ₜ-refl {term _ _} = term ≈ₜ-refl-args

    mutual
      ≈ₜ-sym-args : ∀ {n} {xs ys : Vec _ n}
                    → Pointwise _≈ₜ_ xs ys
                    → Pointwise _≈ₜ_ ys xs
      ≈ₜ-sym-args []       = []
      ≈ₜ-sym-args (p ∷ ps) = ≈ₜ-sym p ∷ ≈ₜ-sym-args ps

      ≈ₜ-sym : ∀ {x y} → x ≈ₜ y → y ≈ₜ x
      ≈ₜ-sym (atom p) = atom (sym p)
      ≈ₜ-sym (term p) = term (≈ₜ-sym-args p)

    mutual
      ≈ₜ-trans-args : ∀ {n} {xs ys zs : Vec _ n}
                    → Pointwise _≈ₜ_ xs ys
                    → Pointwise _≈ₜ_ ys zs
                    → Pointwise _≈ₜ_ xs zs
      ≈ₜ-trans-args []       []       = []
      ≈ₜ-trans-args (p ∷ ps) (q ∷ qs) =
        ≈ₜ-trans p q ∷ ≈ₜ-trans-args ps qs

      ≈ₜ-trans : ∀ {x y z} → x ≈ₜ y → y ≈ₜ z → x ≈ₜ z
      ≈ₜ-trans (atom p) (atom q) = atom (trans p q)
      ≈ₜ-trans (term p) (term q) = term (≈ₜ-trans-args p q)

    ≈ₜ-isEquivalence : IsEquivalence _≈ₜ_
    ≈ₜ-isEquivalence = record { refl  = ≈ₜ-refl
                              ; sym   = ≈ₜ-sym
                              ; trans = ≈ₜ-trans
                              }

    Herbrand : Setoid _ _
    Herbrand = record { Carrier       = Term A
                      ; _≈_           = _≈ₜ_
                      ; isEquivalence = ≈ₜ-isEquivalence
                      }

    term-cong : Congruence Herbrand term
    term-cong f p = term p

    Free-isAlgebra : IsAlgebra Herbrand
    Free-isAlgebra = record { ⟦_⟧     = term
                            ; ⟦⟧-cong = term-cong
                            }

    Free : Algebra
    Free = record { ∥_∥/≈           = Herbrand
                  ; ∥_∥/≈-isAlgebra = Free-isAlgebra
                  }

  atomₛ : ∀ {S : Setoid a ℓ₁} → S →ₛ Herbrand S
  atomₛ = record { ∥_∥ₛ = atom ; ∥_∥ₛ-cong = atom }

  Free≡ : (A : Set a) → Algebra
  Free≡ = Free ∘ PE.setoid

  module _ (A : Algebra {a} {ℓ₁}) where

    open Setoid ∥ A ∥/≈
    open import Relation.Binary.Reasoning.Setoid ∥ A ∥/≈

    mutual
      eval-args-cong : ∀ {n} {xs ys : Vec (Term ∥ A ∥) n}
                       → Pointwise (_≈ₜ_ ∥ A ∥/≈) xs ys
                       → Pointwise ≈[ A ] (eval-args A xs)
                                          (eval-args A ys)
      eval-args-cong []       = []
      eval-args-cong (p ∷ ps) = eval-cong p ∷ eval-args-cong ps

      eval-cong : Congruent (_≈ₜ_ ∥ A ∥/≈) ≈[ A ] (eval A)
      eval-cong (atom p)                 = p
      eval-cong {x = term op _} (term p) = (A ⟦⟧-cong) op (eval-args-cong p)

    eval-args≡map : ∀ {n} {xs : Vec (Term ∥ A ∥) n}
                    → Pointwise _≈_ (eval-args A xs) (map (eval A) xs)
    eval-args≡map {xs = []}     = []
    eval-args≡map {xs = x ∷ xs} = refl ∷ eval-args≡map

    eval-hom : Homomorphic (Free ∥ A ∥/≈) A (eval A)
    eval-hom f []       = refl
    eval-hom f (x ∷ xs) = sym ((A ⟦⟧-cong) f (eval-args≡map {xs = x ∷ xs}))

    evalₕ : Free ∥ A ∥/≈ →ₕ A
    evalₕ = record { ∥_∥ₕ      = eval A
                   ; ∥_∥ₕ-cong = eval-cong
                   ; ∥_∥ₕ-hom  = eval-hom
                   }

  module _
    {A : Setoid a ℓ₁}
    {B : Setoid b ℓ₂}
    (f : A →ₛ Herbrand B)
    where

    mutual
      bind-args-cong : ∀ {n} {xs ys : Vec ∥ Free A ∥ n}
                       → Pointwise (_≈ₜ_ A) xs ys
                       → Pointwise (_≈ₜ_ B) (bind-args ∥ f ∥ₛ xs)
                                                  (bind-args ∥ f ∥ₛ ys)
      bind-args-cong []       = []
      bind-args-cong (p ∷ ps) = bind-cong p ∷ bind-args-cong ps

      bind-cong : Congruent (_≈ₜ_ A) (_≈ₜ_ B) (bind ∥ f ∥ₛ)
      bind-cong (atom p)                 = ∥ f ∥ₛ-cong p
      bind-cong {x = term op _} (term p) =
        term-cong B op (bind-args-cong p)

    bind-args≡map : ∀ {n} {xs : Vec ∥ Free A ∥ n}
                    → Pointwise (_≈ₜ_ B) (bind-args ∥ f ∥ₛ xs)
                                         (map (bind ∥ f ∥ₛ) xs)
    bind-args≡map {xs = []}     = []
    bind-args≡map {xs = x ∷ xs} = (≈ₜ-refl B) ∷ bind-args≡map

    bind-hom : Homomorphic (Free A) (Free B) (bind ∥ f ∥ₛ)
    bind-hom op []       = ≈ₜ-refl B
    bind-hom op (x ∷ xs) =
      ≈ₜ-sym B (term (bind-args≡map {xs = x ∷ xs}))

    bindₕ : Free A →ₕ Free B
    bindₕ = record { ∥_∥ₕ      = bind ∥ f ∥ₛ
                   ; ∥_∥ₕ-cong = bind-cong
                   ; ∥_∥ₕ-hom  = bind-hom
                   }

  fmap : ∀ {A : Setoid a ℓ₁} {B : Setoid b ℓ₂}
         → A →ₛ B
         → Free A →ₕ Free B
  fmap f = bindₕ (atomₛ ∘ₛ f)

  module _ {A : Setoid a ℓ₁} where

    open Setoid (Herbrand A)
    open import Relation.Binary.Reasoning.Setoid (Herbrand A)

    joinₕ : Free (Herbrand A) →ₕ Free A
    joinₕ = bindₕ idₛ

    unitₗ : ∀ {x} → ∥ ∥ joinₕ ∥ₕₛ ∘ₛ atomₛ ∥ₛ x ≈ x
    unitₗ = refl

{-
    unitᵣ : ∀ {x} → ∥ joinₕ ∘ₕ (fmap atomₛ) ∥ₕ x ≈ x
    unitᵣ {atom x}    = refl
    unitᵣ {term f xs} = {!!}
-}

  substₕ : ∀ {A : Setoid a ℓ₁} (B : Algebra {b} {ℓ₂})
           → (A →ₛ ∥ B ∥/≈) → Free A →ₕ B
  substₕ B θ = (evalₕ B) ∘ₕ bindₕ (atomₛ ∘ₛ θ)
