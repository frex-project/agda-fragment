\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

open import Fragment.Algebra.Signature

module Fragment.Equational.Theory.Laws (Σ : Signature) where

open import Fragment.Equational.Theory.Base using (Eq)

open import Function using (_∘_)
open import Data.Empty using (⊥)
open import Data.Fin using (#_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as PE

open import Fragment.Algebra.Free Σ
open import Fragment.Algebra.Free.Syntax Σ (PE.setoid ⊥)

module _ where

  private
    a = # 0

  dne : ops Σ 1 → Eq Σ 1
  dne ~ = ⟨ ~ ⟩₁ ⟨ ~ ⟩₁ ⟨ a ⟩ , ⟨ a ⟩

module _ (e : ops Σ 0) where

  private
    a = # 0

  idₗ : ops Σ 2 → Eq Σ 1
  idₗ • = ⟨ e ⟩₀ ⟨ • ⟩₂ ⟨ a ⟩ , ⟨ a ⟩

  idᵣ : ops Σ 2 → Eq Σ 1
  idᵣ • = ⟨ a ⟩ ⟨ • ⟩₂ ⟨ e ⟩₀ , ⟨ a ⟩

  anₗ : ops Σ 2 → Eq Σ 1
  anₗ • = ⟨ e ⟩₀ ⟨ • ⟩₂ ⟨ a ⟩ , ⟨ e ⟩₀

  anᵣ : ops Σ 2 → Eq Σ 1
  anᵣ • = ⟨ a ⟩ ⟨ • ⟩₂ ⟨ e ⟩₀ , ⟨ e ⟩₀

  invₗ : ops Σ 1 → ops Σ 2 → Eq Σ 1
  invₗ ~ • = (⟨ ~ ⟩₁ ⟨ a ⟩) ⟨ • ⟩₂ ⟨ a ⟩ , ⟨ e ⟩₀

  invᵣ : ops Σ 1 → ops Σ 2 → Eq Σ 1
  invᵣ ~ • = ⟨ a ⟩ ⟨ • ⟩₂ (⟨ ~ ⟩₁ ⟨ a ⟩) , ⟨ e ⟩₀

module _ where

  private

    a = # 0
    b = # 1
    c = # 2

  hom : ops Σ 1 → ∀ {n} → ops Σ n → Eq Σ n
  hom h {n} f =
      ⟨ h ⟩₁ term f (map ⟨_⟩ (allFin n))
    ,
      term f (map (⟨ h ⟩₁_ ∘ ⟨_⟩) (allFin n))
    where open import Data.Vec using (map; allFin)
\end{code}

%<*laws>
\begin{code}
  comm : ops Σ 2 → Eq Σ 2
  comm • = ⟨ a ⟩ ⟨ • ⟩₂ ⟨ b ⟩ , ⟨ b ⟩ ⟨ • ⟩₂ ⟨ a ⟩

  assoc : ops Σ 2 → Eq Σ 3
  assoc • =
      (⟨ a ⟩ ⟨ • ⟩₂ ⟨ b ⟩) ⟨ • ⟩₂ ⟨ c ⟩
    ,
      ⟨ a ⟩ ⟨ • ⟩₂ (⟨ b ⟩ ⟨ • ⟩₂ ⟨ c ⟩)
\end{code}
%</laws>
