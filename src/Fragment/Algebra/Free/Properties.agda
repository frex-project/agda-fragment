{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Properties (Σ : Signature) where

open import Level using (Level)
open import Function using (_∘_)

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Free.Base Σ
open import Fragment.Algebra.Free.Evaluation Σ
open import Fragment.Algebra.Free.Monad Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Algebra.Initial Σ
open import Fragment.Algebra.Quotient Σ

open import Fragment.Setoid.Morphism as Morphism
  hiding (∣_∣; ∣_∣-cong; id)

open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; Pointwise-≡⇒≡; []; _∷_)

open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  {A : Algebra {a} {ℓ₁}}
  (h : Free ∥ A ∥/≈ ⟿ A)
  (inj : ∣ h ∣⃗ · unit ∻ Morphism.id)
  where

  open Setoid ∥ A ∥/≈
  open import Relation.Binary.Reasoning.Setoid ∥ A ∥/≈

  mutual
    ∣eval∣-args-universal : ∀ {n} {xs : Vec (Term ∥ A ∥) n}
                            → Pointwise (≈[ A ]) (map ∣ h ∣ xs)
                                                 (∣eval∣-args A xs)
    ∣eval∣-args-universal {_} {[]}     = []
    ∣eval∣-args-universal {_} {x ∷ xs} =
      eval-universal {x} ∷ ∣eval∣-args-universal {_} {xs}

    eval-universal : h ≗ eval A
    eval-universal {atom x}    = inj
    eval-universal {term f xs} = begin
        ∣ h ∣ (term f xs)
      ≈⟨ sym (∣ h ∣-hom f xs) ⟩
        A ⟦ f ⟧ (map ∣ h ∣ xs)
      ≈⟨ (A ⟦ f ⟧-cong) ∣eval∣-args-universal ⟩
        A ⟦ f ⟧ (∣eval∣-args A xs)
      ∎

module _
  {A : Setoid a ℓ₁}
  {B : Setoid b ℓ₂}
  (f : A ↝ Herbrand B)
  where

  bind-unitₗ : ∣ bind f ∣⃗ · unit ∻ f
  bind-unitₗ = Setoid.refl (Herbrand B)

module _ {A : Setoid a ℓ₁} where

  mutual
    ∣bind∣-args-unitʳ : ∀ {n} → {xs : Vec ∥ Free A ∥ n}
                        → Pointwise (_∼_ A) (∣bind∣-args atom xs) xs
    ∣bind∣-args-unitʳ {xs = []}     = []
    ∣bind∣-args-unitʳ {xs = x ∷ xs} = bind-unitʳ ∷ ∣bind∣-args-unitʳ

    bind-unitʳ : bind {B = A} unit ≗ id
    bind-unitʳ {atom _}   = Setoid.refl (Herbrand A)
    bind-unitʳ {term _ _} = term ∣bind∣-args-unitʳ

module _
  {A : Setoid a ℓ₁}
  {B : Setoid b ℓ₂}
  {C : Setoid c ℓ₃}
  (g : B ↝ Herbrand C)
  (f : A ↝ Herbrand B)
  where

  open Setoid (Herbrand C)

  private
    ∣g∣ = Morphism.∣ g ∣
    ∣f∣ = Morphism.∣ f ∣

  mutual
    ∣bind∣-args-assoc : ∀ {n} → {xs : Vec ∥ Free A ∥ n}
                        → Pointwise (_∼_ C)
                                    (∣bind∣-args ∣g∣ (∣bind∣-args ∣f∣ xs))
                                    (∣bind∣-args (∣ bind g ∣ ∘ ∣f∣) xs)
    ∣bind∣-args-assoc {xs = []}     = []
    ∣bind∣-args-assoc {xs = x ∷ xs} =
      bind-assoc {x} ∷ ∣bind∣-args-assoc

    bind-assoc : bind g ⊙ bind f ≗ bind (∣ bind g ∣⃗ · f)
    bind-assoc {atom _}   = refl
    bind-assoc {term _ _} = term ∣bind∣-args-assoc

module _ {A : Setoid a ℓ₁} where

  open Setoid (Herbrand A)

  fmap-id : fmap Morphism.id ≗ id
  fmap-id = bind-unitʳ {A = A}


module _ {n}
  (A : Algebra {a} {ℓ₁})
  (θ : Env A n)
  where

  IsInstantiation : F n ⟿ A → Set _
  IsInstantiation f = ∀ x → ∣ f ∣ (atom (dyn x)) ≡ θ x

  inst-isInstantiation : IsInstantiation (inst A θ)
  inst-isInstantiation x = PE.refl

  mutual
    map-inst-universal : ∀ {h m} → IsInstantiation h
                         → {xs : Vec ∥ F n ∥ m}
                         → Pointwise ≈[ A ] (map ∣ h ∣ xs)
                                            (map ∣ inst A θ ∣ xs)
    map-inst-universal p {xs = []}             = []
    map-inst-universal {h = h} p {xs = x ∷ xs} =
      inst-universal {h = h} p ∷ map-inst-universal {h = h} p

    inst-universal : ∀ {h} → IsInstantiation h → h ≗ (inst A θ)
    inst-universal {h} p {x = atom (dyn x)} = Setoid.reflexive ∥ A ∥/≈ (p x)
    inst-universal {h} p {x = term f xs}    = begin
        ∣ h ∣ (term f xs)
      ≈⟨ Setoid.sym ∥ A ∥/≈ (∣ h ∣-hom f xs) ⟩
        A ⟦ f ⟧ (map ∣ h ∣ xs)
      ≈⟨ (A ⟦ f ⟧-cong) (map-inst-universal {h = h} p {xs = xs}) ⟩
        A ⟦ f ⟧ (map ∣ inst A θ ∣ xs)
      ≈⟨ ∣ inst A θ ∣-hom f xs ⟩
        ∣ inst A θ ∣ (term f xs)
      ∎
      where open import Relation.Binary.Reasoning.Setoid ∥ A ∥/≈

  module _
    {B : Algebra {b} {ℓ₂}}
    (h : A ⟿ B)
    where

    mutual
      map-inst-assoc : ∀ {m} {xs : Vec ∥ F n ∥ m}
                       → Pointwise ≈[ B ]
                                   (map ∣ h ⊙ inst A θ ∣ xs)
                                   (map ∣ inst B (∣ h ∣ ∘ θ) ∣ xs)
      map-inst-assoc {xs = []}     = []
      map-inst-assoc {xs = x ∷ xs} = inst-assoc {x = x} ∷ map-inst-assoc

      inst-assoc : h ⊙ inst A θ ≗ inst B (∣ h ∣ ∘ θ)
      inst-assoc {atom (dyn _)} = Setoid.refl ∥ B ∥/≈
      inst-assoc {term f xs}    = begin
          ∣ h ⊙ inst A θ ∣ (term f xs)
        ≈⟨ sym (∣ h ⊙ inst A θ ∣-hom f xs) ⟩
          B ⟦ f ⟧ (map ∣ h ⊙ inst A θ ∣ xs)
        ≈⟨ (B ⟦ f ⟧-cong) map-inst-assoc ⟩
          B ⟦ f ⟧ (map ∣ inst B (∣ h ∣ ∘ θ) ∣ xs)
        ≈⟨ ∣ inst B (∣ h ∣ ∘ θ) ∣-hom f xs ⟩
          ∣ inst B (∣ h ∣ ∘ θ) ∣ (term f xs)
        ∎
        where open Setoid ∥ B ∥/≈
              open import Relation.Binary.Reasoning.Setoid ∥ B ∥/≈
