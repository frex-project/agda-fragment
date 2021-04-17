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

open import Relation.Binary using (Setoid; Rel)
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
  {A : Algebra {a} {ℓ₁}}
  (_≈_ : Rel ∥ A ∥ ℓ₃)
  {{isDenom : IsDenominator A _≈_}}
  where

  mutual
    ∣eval∣-args-quot : ∀ {n} {xs : Vec (Term ∥ A ∥) n}
                       → Pointwise _≡_ (∣eval∣-args A xs)
                                       (∣eval∣-args (A / _≈_) xs)
    ∣eval∣-args-quot {xs = []}     = []
    ∣eval∣-args-quot {xs = x ∷ xs} = ∣eval∣-quot {x} ∷ ∣eval∣-args-quot

    ∣eval∣-quot : ∀ {x} → ∣ eval A ∣ x ≡ ∣ eval (A / _≈_) ∣ x
    ∣eval∣-quot {atom _}   = PE.refl
    ∣eval∣-quot {term f _} =
      PE.cong (A ⟦ f ⟧_) (Pointwise-≡⇒≡ ∣eval∣-args-quot)

  ∣inst∣-quot : ∀ {n x} (θ : Env A n)
                → ∣ inst A θ ∣ x ≡ ∣ inst (A / _≈_) θ ∣ x
  ∣inst∣-quot {x = x} θ =
    ∣eval∣-quot {x = ∣ bind {B = ∥ A ∥/≈} (unit · (lift θ)) ∣ x}

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

module _ {p q}
 {A : Algebra {a} {ℓ₁}}
 (θ : Env A p)
 (θ' : Env (F p) q)
 where

 open Setoid ∥ A ∥/≈

 mutual
   ∣inst∣-args-assoc : ∀ {n} {xs : Vec ∥ F q ∥ n}
                       → Pointwise ≈[ A ]
                                   (∣inst∣-args A θ (∣inst∣-args (F p) θ' xs))
                                   (∣inst∣-args A (∣ inst A θ ∣ ∘ θ') xs)
   ∣inst∣-args-assoc {xs = []}     = []
   ∣inst∣-args-assoc {xs = x ∷ xs} = inst-assoc {x = x} ∷ ∣inst∣-args-assoc

   inst-assoc : inst A θ ⊙ (inst (F p) θ') ≗ inst A (∣ inst A θ ∣ ∘ θ')
   inst-assoc {atom _}   = refl
   inst-assoc {term f _} = (A ⟦ f ⟧-cong) ∣inst∣-args-assoc
