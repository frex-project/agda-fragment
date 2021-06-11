{-# OPTIONS --without-K --exact-split --safe #-}

module Fragment.Extensions.CSemigroup.Nat where

open import Relation.Binary.PropositionalEquality as PE using (_≡_)

data ℕ⁺ : Set where
  one : ℕ⁺
  suc : ℕ⁺ → ℕ⁺

infixl 6 _+_

_+_ : ℕ⁺ → ℕ⁺ → ℕ⁺
one   + x = suc x
suc x + y = suc (x + y)

+-suc : ∀ x y → x + suc y ≡ suc (x + y)
+-suc one     y = PE.refl
+-suc (suc x) y = PE.cong suc (+-suc x y)

+-one : ∀ x → x + one ≡ suc x
+-one one     = PE.refl
+-one (suc x) = PE.cong suc (+-one x)

+-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
+-assoc one     _ _ = PE.refl
+-assoc (suc x) y z = PE.cong suc (+-assoc x y z)

open PE.≡-Reasoning

+-comm : ∀ x y → x + y ≡ y + x
+-comm one one     = PE.refl
+-comm one (suc y) = begin
    one + (suc y) ≡⟨⟩
    suc (suc y)   ≡⟨ PE.sym (PE.cong suc (+-one y)) ⟩
    suc (y + one) ≡⟨ PE.sym PE.refl ⟩
    suc y + one   ∎
+-comm (suc x) y = begin
    suc x + y     ≡⟨⟩
    suc (x + y)   ≡⟨ PE.cong suc (+-comm x y) ⟩
    suc (y + x)   ≡⟨ PE.sym (+-suc y x) ⟩
    y + suc x     ∎
