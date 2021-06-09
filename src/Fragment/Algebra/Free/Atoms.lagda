\begin{code}[hidden]
{-# OPTIONS --without-K --safe #-}

module Fragment.Algebra.Free.Atoms where

open import Level using (Level; _⊔_)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level
\end{code}

%<*bt>
\begin{code}
data BT (A : Set a) (n : ℕ) : Set a where
  sta : A → BT A n
  dyn : Fin n → BT A n
\end{code}
%</bt>

\begin{code}[hidden]
module _ (S : Setoid a ℓ) (n : ℕ) where

  open Setoid S renaming (Carrier to A)
\end{code}

%<*bteq>
\begin{code}
  data _≍_ : BT A n → BT A n → Set (a ⊔ ℓ) where
    sta : ∀ {x y} → x ≈ y → sta x ≍ sta y
    dyn : ∀ {x y} → x ≡ y → dyn x ≍ dyn y
\end{code}
%</bteq>

\begin{code}[hidden]
  private

    ≍-refl : ∀ {x} → x ≍ x
    ≍-refl {sta _} = sta refl
    ≍-refl {dyn _} = dyn PE.refl

    ≍-sym : ∀ {x y} → x ≍ y → y ≍ x
    ≍-sym (sta x≈y) = sta (sym x≈y)
    ≍-sym (dyn x≡y) = dyn (PE.sym x≡y)

    ≍-trans : ∀ {x y z} → x ≍ y → y ≍ z → x ≍ z
    ≍-trans (sta x≈y) (sta y≈z) = sta (trans x≈y y≈z)
    ≍-trans (dyn x≡y) (dyn y≡z) = dyn (PE.trans x≡y y≡z)

    ≍-isEquivalence : IsEquivalence _≍_
    ≍-isEquivalence = record { refl  = ≍-refl
                             ; sym   = ≍-sym
                             ; trans = ≍-trans
                             }
\end{code}[hidden]

%<*atoms>
\begin{code}
  Atoms : Setoid a (a ⊔ ℓ)
  Atoms = record { Carrier       = BT (Setoid.Carrier S) n
                 ; _≈_           = _≍_
                 ; isEquivalence = ≍-isEquivalence
                 }
\end{code}
%</atoms>
