\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Theory

module Fragment.Equational.Model.Base (Θ : Theory) where

open import Fragment.Equational.Model.Satisfaction {Σ Θ}
open import Fragment.Algebra.Algebra (Σ Θ) hiding (∥_∥/≈)
open import Fragment.Algebra.Free (Σ Θ)

open import Level using (Level; _⊔_; suc)
open import Function using (_∘_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Binary using (Setoid)

private
  variable
    a ℓ : Level
\end{code}

%<*models>
\begin{code}
Models : Algebra {a} {ℓ} → Set (a ⊔ ℓ)
Models S = ∀ {n} → (eq : eqs Θ n) → S ⊨ (Θ ⟦ eq ⟧ₑ)
\end{code}
%</models>

\begin{code}[hidden]
module _ (S : Setoid a ℓ) where
\end{code}

%<*ismodel>
\begin{code}
  record IsModel : Set (a ⊔ ℓ) where
    field
      isAlgebra : IsAlgebra S
      models    : Models (algebra S isAlgebra)
\end{code}
%</ismodel>
\begin{code}
    open IsAlgebra isAlgebra public
\end{code}

%<*model>
\begin{code}
record Model : Set (suc a ⊔ suc ℓ) where
  field
    ∥_∥/≈   : Setoid a ℓ
    isModel : IsModel ∥_∥/≈
\end{code}
%</model>

\begin{code}[hidden]
  ∥_∥ₐ : Algebra
  ∥_∥ₐ = record { ∥_∥/≈ = ∥_∥/≈
                ; ∥_∥/≈-isAlgebra = IsModel.isAlgebra isModel
                }

  ∥_∥ₐ-models : Models ∥_∥ₐ
  ∥_∥ₐ-models = IsModel.models isModel

  open Algebra ∥_∥ₐ hiding (∥_∥/≈) public

open Model public
\end{code}
