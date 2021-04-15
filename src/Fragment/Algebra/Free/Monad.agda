{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Monad (Σ : Signature) where

open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ
open import Fragment.Setoid.Morphism as Morphism
open import Fragment.Algebra.Free.Base Σ

open import Level using (Level)

open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
  using (Pointwise; []; _∷_)

open import Relation.Binary using (Setoid)

private
  variable
    a b ℓ₁ ℓ₂ : Level

unit : ∀ {S : Setoid a ℓ₁} → S ↝ Herbrand S
unit = record { ∣_∣      = atom
              ; ∣_∣-cong = atom
              }

module _ {A : Set a} {B : Set b} where

  mutual
    ∣bind∣-args : ∀ {n} → (A → Term B)
                  → Vec (Term A) n → Vec (Term B) n
    ∣bind∣-args f []       = []
    ∣bind∣-args f (x ∷ xs) = ∣bind∣ f x ∷ ∣bind∣-args f xs

    ∣bind∣ : (A → Term B) → Term A → Term B
    ∣bind∣ f (atom x)     = f x
    ∣bind∣ f (term op xs) = term op (∣bind∣-args f xs)

module _
  {A : Setoid a ℓ₁}
  {B : Setoid b ℓ₂}
  (f : A ↝ Herbrand B)
  where

  mutual
    ∣bind∣-args-cong : ∀ {n} {xs ys : Vec ∥ Free A ∥ n}
                       → Pointwise (_∼_ A) xs ys
                       → Pointwise (_∼_ B) (∣bind∣-args Morphism.∣ f ∣ xs)
                                           (∣bind∣-args Morphism.∣ f ∣ ys)
    ∣bind∣-args-cong []       = []
    ∣bind∣-args-cong (p ∷ ps) = ∣bind∣-cong p ∷ ∣bind∣-args-cong ps

    ∣bind∣-cong : Congruent (_∼_ A) (_∼_ B) (∣bind∣ Morphism.∣ f ∣)
    ∣bind∣-cong (atom p)                 = Morphism.∣ f ∣-cong p
    ∣bind∣-cong {x = term op _} (term p) =
      term-cong B op (∣bind∣-args-cong p)

  ∣bind∣-args≡map : ∀ {n} {xs : Vec ∥ Free A ∥ n}
                    → Pointwise (_∼_ B) (∣bind∣-args Morphism.∣ f ∣ xs)
                                        (map (∣bind∣ Morphism.∣ f ∣) xs)
  ∣bind∣-args≡map {xs = []}     = []
  ∣bind∣-args≡map {xs = x ∷ xs} = (∼-refl B) ∷ ∣bind∣-args≡map

  ∣bind∣-hom : Homomorphic (Free A) (Free B) (∣bind∣ Morphism.∣ f ∣)
  ∣bind∣-hom op []       = ∼-refl B
  ∣bind∣-hom op (x ∷ xs) =
    ∼-sym B (term (∣bind∣-args≡map {xs = x ∷ xs}))

  ∣bind∣⃗ : Herbrand A ↝ Herbrand B
  ∣bind∣⃗ = record { ∣_∣      = ∣bind∣ Morphism.∣ f ∣
                   ; ∣_∣-cong = ∣bind∣-cong
                   }

  bind : Free A ⟿ Free B
  bind = record { ∣_∣⃗    = ∣bind∣⃗
                ; ∣_∣-hom = ∣bind∣-hom
                }

fmap : ∀ {A : Setoid a ℓ₁} {B : Setoid b ℓ₂}
       → A ↝ B
       → Free A ⟿ Free B
fmap f = bind (unit · f)

join : ∀ {A : Setoid a ℓ₁} → Free (Herbrand A) ⟿ Free A
join = bind Morphism.id
