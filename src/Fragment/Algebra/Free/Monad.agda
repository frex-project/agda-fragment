{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Algebra.Free.Monad (Σ : Signature) where

open import Fragment.Algebra.Free.Base Σ
open import Fragment.Algebra.Algebra Σ
open import Fragment.Algebra.Homomorphism Σ using (_⟿_; Congruent; Homomorphic)
open import Fragment.Setoid.Morphism

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

module _
  {A : Setoid a ℓ₁}
  {B : Setoid b ℓ₂}
  (f : A ↝ Herbrand B)
  where

  private

    open Setoid ∥ Free B ∥/≈

    module _ {A : Set a} {B : Set b} where

      mutual
        map-∣bind∣ : ∀ {n} → (A → Term B)
                 → Vec (Term A) n → Vec (Term B) n
        map-∣bind∣ f []       = []
        map-∣bind∣ f (x ∷ xs) = ∣bind∣ f x ∷ map-∣bind∣ f xs

        ∣bind∣ : (A → Term B) → Term A → Term B
        ∣bind∣ f (atom x)     = f x
        ∣bind∣ f (term op xs) = term op (map-∣bind∣ f xs)

    mutual
      map-∣bind∣-cong : ∀ {n} {xs ys : Vec ∥ Free A ∥ n}
                        → Pointwise (_~_ A) xs ys
                        → Pointwise (_~_ B) (map-∣bind∣ ∣ f ∣ xs)
                                            (map-∣bind∣ ∣ f ∣ ys)
      map-∣bind∣-cong []       = []
      map-∣bind∣-cong (p ∷ ps) = ∣bind∣-cong p ∷ map-∣bind∣-cong ps

      ∣bind∣-cong : Congruent (_~_ A) (_~_ B) (∣bind∣ ∣ f ∣)
      ∣bind∣-cong (atom p)                 = ∣ f ∣-cong p
      ∣bind∣-cong {x = term op _} (term p) = term (map-∣bind∣-cong p)

    map-∣bind∣≡map : ∀ {n} {xs : Vec ∥ Free A ∥ n}
                     → Pointwise (_~_ B) (map-∣bind∣ ∣ f ∣ xs)
                                         (map (∣bind∣ ∣ f ∣) xs)
    map-∣bind∣≡map {xs = []}     = []
    map-∣bind∣≡map {xs = x ∷ xs} = refl ∷ map-∣bind∣≡map

    ∣bind∣-hom : Homomorphic (Free A) (Free B) (∣bind∣ ∣ f ∣)
    ∣bind∣-hom op []       = refl
    ∣bind∣-hom op (x ∷ xs) = sym (term (map-∣bind∣≡map {xs = x ∷ xs}))

    ∣bind∣⃗ : Herbrand A ↝ Herbrand B
    ∣bind∣⃗ = record { ∣_∣      = ∣bind∣ ∣ f ∣
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
join = bind id
