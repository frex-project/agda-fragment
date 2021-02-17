{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Bundles
  using (Θ-semigroup; Σ-magma; MagmaOp; SemigroupEq)
open import Fragment.Equational.Model

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

module Fragment.Extensions.Semigroup {a}
  {A : Set a}
  (isModel : IsModel Θ-semigroup (PE.setoid A))
  where

open import Fragment.Equational.Structures using (isModel→semigroup)
open import Fragment.Equational.FreeExtension Θ-semigroup

open import Fragment.Algebra.Algebra

open import Algebra.Structures using (IsSemigroup)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; #_)
open import Data.Vec using (Vec; _∷_; [])
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)

open IsModel isModel
open IsSemigroup (isModel→semigroup (PE.setoid A) isModel)

private
  M : Model Θ-semigroup
  M = record { Carrierₛ = (PE.setoid A)
             ; isModel  = isModel
             }

open PE.≡-Reasoning

_•_ : A → A → A
x • y = ⟦ MagmaOp.• ⟧ (x ∷ y ∷ [])

data Semigroup (n : ℕ) : Set a where
  leaf : A ⊎ Fin n → Semigroup n
  cons : A ⊎ Fin n → Semigroup n → Semigroup n

consS : ∀ {n} → A → Semigroup n → Semigroup n
consS a (leaf (inj₁ x))    = leaf (inj₁ (a • x))
consS a (cons (inj₁ x) xs) = cons (inj₁ (a • x)) xs
consS a x                  = cons (inj₁ a) x

consD : ∀ {n} → Fin n → Semigroup n → Semigroup n
consD a x = cons (inj₂ a) x

normalise : ∀ {n} → Semigroup n → Semigroup n
normalise (cons (inj₁ x) xs) = consS x (normalise xs)
normalise (cons (inj₂ x) xs) = consD x (normalise xs)
normalise x                  = x

data Normal {n} : Semigroup n → Set a where
  leaf  : ∀ {x} → Normal (leaf x)
  cons₁ : ∀ {x y} → Normal (cons (inj₁ x) (leaf (inj₂ y)))
  cons₂ : ∀ {x xs} → Normal xs → Normal (cons (inj₂ x) xs)
  cons₃ : ∀ {x y ys} → Normal ys → Normal (cons (inj₁ x) (cons (inj₂ y) ys))

consS-preserves : ∀ {n x xs} → Normal {n} xs → Normal {n} (consS x xs)
consS-preserves (leaf {x = inj₁ y}) = leaf
consS-preserves (leaf {x = inj₂ y}) = cons₁
consS-preserves cons₁     = cons₁
consS-preserves (cons₂ p) = cons₃ p
consS-preserves (cons₃ p) = cons₃ p

normalise-reduction : ∀ {n x} → Normal {n} (normalise x)
normalise-reduction {x = leaf x}           = leaf
normalise-reduction {x = cons (inj₁ x) xs} = consS-preserves (normalise-reduction {x = xs})
normalise-reduction {x = cons (inj₂ x) xs} = cons₂ (normalise-reduction {x = xs})

_++-raw_ : ∀ {n} → Semigroup n → Semigroup n → Semigroup n
leaf (inj₁ x)    ++-raw y = consS x y
leaf (inj₂ x)    ++-raw y = consD x y
cons (inj₁ x) xs ++-raw y = consS x (xs ++-raw y)
cons (inj₂ x) xs ++-raw y = consD x (xs ++-raw y)

++-preserves : ∀ {n x y}
               → Normal {n} x
               → Normal y
               → Normal (x ++-raw y)
++-preserves {x = leaf (inj₁ x)} {y = y} leaf q                = consS-preserves q
++-preserves {x = leaf (inj₂ x)} {y = y} leaf q                = cons₂ q
++-preserves {x = cons (inj₁ x) (leaf (inj₂ _))} cons₁ q       = cons₃ q
++-preserves {x = cons (inj₁ x) (cons (inj₂ _) _)} (cons₃ p) q = cons₃ (++-preserves p q)
++-preserves {x = cons (inj₂ x) xs} {y = y} (cons₂ p) q        = cons₂ (++-preserves p q)

NormalSemigroup : ℕ → Set a
NormalSemigroup n = Σ[ x ∈ Semigroup n ] (Normal x)

_++_ : ∀ {n} → NormalSemigroup n → NormalSemigroup n → NormalSemigroup n
( x , p ) ++ ( y , q ) =  x ++-raw y , ++-preserves p q

++-assoc : ∀ {n} → (x y z : NormalSemigroup n)
           → (x ++ y) ++ z ≡ x ++ (y ++ z)
++-assoc x y z = {!!}

++-⟦_⟧ : ∀ {n} → Interpretation Σ-magma (PE.setoid (NormalSemigroup n))
++-⟦_⟧ {n} MagmaOp.• (x ∷ y ∷ []) = _++_ {n} x y

++-⟦⟧-cong : ∀ {n} → Congruence Σ-magma (PE.setoid (NormalSemigroup n)) (++-⟦_⟧ {n})
++-⟦⟧-cong {n} MagmaOp.• p = PE.cong (++-⟦_⟧ {n} MagmaOp.•) (≋⇒≡ p)

++-isAlgebra : ∀ {n} → IsAlgebra Σ-magma (PE.setoid (NormalSemigroup n))
++-isAlgebra {n} = record { ⟦_⟧     = ++-⟦_⟧ {n}
                          ; ⟦⟧-cong = ++-⟦⟧-cong {n}
                          }

++-algebra : ∀ {n} → Algebra Σ-magma
++-algebra {n} = algebra (PE.setoid (NormalSemigroup n)) (++-isAlgebra {n})

++-models : ∀ {n} → Models Θ-semigroup (++-algebra {n})
++-models {n} SemigroupEq.assoc {θ} = ++-assoc {n} (θ (# 0)) (θ (# 1)) (θ (# 2))

++-isModel : ∀ {n} → IsModel Θ-semigroup (PE.setoid (NormalSemigroup n))
++-isModel {n} = record { isAlgebra = ++-isAlgebra {n}
                        ; models    = ++-models {n}
                        }

++-model : ∀ {n} → Model Θ-semigroup
++-model {n} = record { Carrierₛ = PE.setoid (NormalSemigroup n)
                      ; isModel  = ++-isModel {n}
                      }

++-isFrex : ∀ {n} → IsFreeExtension M n (++-model {n})
++-isFrex {n} = record { inl       = {!!}
                       ; inr       = {!!}
                       ; [_,_]     = {!!}
                       ; commute₁  = {!!}
                       ; commute₂  = {!!}
                       ; universal = {!!}
                       }
