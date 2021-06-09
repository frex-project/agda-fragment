\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Homomorphism.Base (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism.Definitions Σ

open import Fragment.Setoid.Morphism as Morphism
  hiding (id; ∣_∣; ∣_∣-cong)

open import Level using (Level; _⊔_)
open import Function using (_∘_; _$_)

open import Data.Vec using (map)
open import Data.Vec.Properties using (map-id; map-∘)
import Data.Vec.Relation.Binary.Equality.Setoid as VecSetoid

open import Relation.Binary using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as Reasoning

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module _
  (A : Algebra {a} {ℓ₁})
  (B : Algebra {b} {ℓ₂})
  where

  infixr 1 _⟿_
\end{code}

%<*homomorphism>
\begin{code}
  record _⟿_ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      ∣_∣⃗    : ∥ A ∥/≈ ↝ ∥ B ∥/≈
      ∣_∣-hom : Homomorphic A B (Morphism.∣_∣ ∣_∣⃗)
\end{code}
%</homomorphism>

\begin{code}[hidden]
    ∣_∣ : ∥ A ∥ → ∥ B ∥
    ∣_∣ = Morphism.∣_∣ ∣_∣⃗

    ∣_∣-cong : Congruent ≈[ A ] ≈[ B ] ∣_∣
    ∣_∣-cong = Morphism.∣_∣-cong ∣_∣⃗

open _⟿_ public

module _ {A : Algebra {a} {ℓ₁}} where

  private

    ∣id∣-hom : Homomorphic A A (λ x → x)
    ∣id∣-hom {n} f xs = A ⟦ f ⟧-cong $ reflexive (map-id xs)
      where open VecSetoid ∥ A ∥/≈
            open IsEquivalence (≋-isEquivalence n) using (reflexive)

  id : A ⟿ A
  id = record { ∣_∣⃗    = Morphism.id
              ; ∣_∣-hom = ∣id∣-hom
              }

module _
  {A : Algebra {a} {ℓ₁}}
  {B : Algebra {b} {ℓ₂}}
  {C : Algebra {c} {ℓ₃}}
  (g : B ⟿ C)
  (f : A ⟿ B)
  where

  private

    ⊙-hom : Homomorphic A C (∣ g ∣ ∘ ∣ f ∣)
    ⊙-hom {n} op xs = begin
        C ⟦ op ⟧ (map (∣ g ∣ ∘ ∣ f ∣) xs)
      ≈⟨ C ⟦ op ⟧-cong $ reflexive (map-∘ ∣ g ∣ ∣ f ∣ xs) ⟩
        C ⟦ op ⟧ (map ∣ g ∣ (map ∣ f ∣ xs))
      ≈⟨ ∣ g ∣-hom op (map ∣ f ∣ xs) ⟩
        ∣ g ∣ (B ⟦ op ⟧ (map ∣ f ∣ xs))
      ≈⟨ ∣ g ∣-cong (∣ f ∣-hom op xs) ⟩
        ∣ g ∣ (∣ f ∣ (A ⟦ op ⟧ xs))
      ∎
      where open Reasoning ∥ C ∥/≈
            open VecSetoid ∥ C ∥/≈
            open IsEquivalence (≋-isEquivalence n) using (reflexive)

  infixr 9 _⊙_

  _⊙_ : A ⟿ C
  _⊙_ = record { ∣_∣⃗    = ∣ g ∣⃗ · ∣ f ∣⃗
               ; ∣_∣-hom = ⊙-hom
               }
\end{code}
