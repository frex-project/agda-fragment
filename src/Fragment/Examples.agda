{-# OPTIONS --without-K --safe #-}

module Fragment.Examples where

open import Fragment.Prelude

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Data.Nat using (ℕ; _+_)
open import Data.Vec using ([]; _∷_)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Nat.Properties using (+-isSemigroup)

open import Relation.Binary using (Setoid; IsEquivalence)

open import Fragment.Equational.Model Θ-semigroup
open import Fragment.Algebra.Free.Syntax Σ-magma (PE.setoid ℕ)
open import Fragment.Equational.FreeExtension using (FreeExtension; frexify)

simple : ∀ {f : ℕ → ℕ} {m n} → (f m + 2) + (3 + n) ≡ (f m + 5) + n
simple {f} {m} {n} = frexify Θ-semigroup
                             SemigroupFrex
                             model
                             2
                             (f m ∷ n ∷ [])
                             {lhs = (⟨ # 0 ⟩ ⟨ • ⟩₂ ⟨ 2 ⟩ₛ) ⟨ • ⟩₂ (⟨ 3 ⟩ₛ ⟨ • ⟩₂ ⟨ # 1 ⟩)}
                             {rhs = (⟨ # 0 ⟩ ⟨ • ⟩₂ ⟨ 5 ⟩ₛ) ⟨ • ⟩₂ ⟨ # 1 ⟩}
                             (Setoid.refl ∥ FreeExtension._[_] SemigroupFrex model 2 ∥/≈)
  where model = semigroup→model +-isSemigroup

{-
infix 5 _≈_

data _≈_ : ℕ → ℕ → Set where
  refl  : ∀ {n m} → n ≡ m → n ≈ m
  glueₗ : 0 ≈ 1
  glueᵣ : 1 ≈ 0

≈-sym : ∀ {n m} → n ≈ m → m ≈ n
≈-sym (refl p)  = refl (PE.sym p)
≈-sym glueₗ     = glueᵣ
≈-sym glueᵣ     = glueₗ

≈-trans : ∀ {n m o} → n ≈ m → m ≈ o → n ≈ o
≈-trans         (refl p)  (refl q) = refl (PE.trans p q)
≈-trans         glueₗ     glueᵣ    = refl PE.refl
≈-trans         glueᵣ     glueₗ    = refl PE.refl
≈-trans {n = 0} (refl p)  glueₗ    = glueₗ
≈-trans {n = 1} (refl p)  glueᵣ    = glueᵣ
≈-trans {o = 1} glueₗ     (refl q) = glueₗ
≈-trans {o = 0} glueᵣ     (refl q) = glueᵣ

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence = record { refl  = refl PE.refl
                         ; sym   = ≈-sym
                         ; trans = ≈-trans
                         }

{- Note we never prove this is decidable -}
≈-setoid : Setoid _ _
≈-setoid = record { Carrier       = ℕ
                  ; _≈_           = _≈_
                  ; isEquivalence = ≈-isEquivalence
                  }

open import Algebra.Structures _≈_
open import Algebra.Definitions _≈_

left : ℕ → ℕ → ℕ
left 0 y = 1
left x y = x

left-cong₂ : ∀ {n m o p} → n ≈ m → o ≈ p → left n o ≈ left m p
left-cong₂ {n = 0} {m = 0} (refl p) _ = refl (PE.refl)
left-cong₂ {n = 0} {m = 1} glueₗ _    = refl (PE.refl)
left-cong₂ {n = 1} {m = 0} glueᵣ _    = refl (PE.refl)
left-cong₂ {n = suc n} {m = suc m} (refl p) _ = refl p

left-assoc : ∀ x y z → left (left x y) z ≈ left x (left y x)
left-assoc 0 y z       = refl PE.refl
left-assoc (suc n) y z = refl PE.refl

left-isMagma : IsMagma left
left-isMagma =
  record { isEquivalence = ≈-isEquivalence
         ; ∙-cong        = left-cong₂
         }

left-isSemigroup : IsSemigroup left
left-isSemigroup =
  record { isMagma = left-isMagma
         ; assoc   = left-assoc
         }

left-test : ∀ {m n} → left (left m n) (left m n) ≈ left m (left n (left m n))
left-test = fragment SemigroupFrex (semigroup→model left-isSemigroup)

simple : ∀ {m n} → (m + 2) + (3 + n) ≡ (m + 5) + n
simple = fragment SemigroupFrex (semigroup→model +-isSemigroup)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-isSemigroup)

lists : ∀ {m n x y}
        → ((0 ∷ m) ++ (x ∷ [])) ++ ((y ∷ []) ++ n)
          ≡ (0 ∷ m) ++ (x ∷ y ∷ []) ++ n
lists = fragment SemigroupFrex (semigroup→model (++-isSemigroup {A = ℕ}))
-}
