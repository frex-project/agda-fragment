{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.CSemigroup where

open import Fragment.Equational.Theory.Bundles

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence)

open import Fragment.Equational.FreeExtension Θ-csemigroup
open import Fragment.Equational.Model Θ-csemigroup

open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level; _⊔_)

open import Data.Nat using (ℕ; _+_; zero; suc; _≤_; z≤n)
open import Data.Nat.Properties using (m≤m+n; ≤-poset; +-comm; +-assoc; +-identityˡ)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; zipWith; lookup; replicate; updateAt)
open import Data.Vec.Properties
  using (lookup-zipWith; zipWith-comm; zipWith-assoc; zipWith-identityˡ; lookup∘updateAt)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning

private
  variable
    a ℓ : Level

  NonEmpty : ∀ {n} → Vec ℕ n → Set
  NonEmpty {n} xs = Σ[ i ∈ Fin n ] (0 ≤ lookup xs i)

  merge : ∀ {n} → Vec ℕ n → Vec ℕ n → Vec ℕ n
  merge xs ys = zipWith _+_ xs ys

  merge-comm : ∀ {n} (x y : Vec ℕ n) → merge x y ≡ merge y x
  merge-comm = zipWith-comm +-comm

  merge-assoc : ∀ {n} (x y z : Vec ℕ n)
                → merge (merge x y) z ≡ merge x (merge y z)
  merge-assoc = zipWith-assoc +-assoc

  merge-preserves : ∀ {n} {b c : Vec ℕ n}
                    → NonEmpty b → NonEmpty c
                    → NonEmpty (merge b c)
  merge-preserves {b = b} {c = c} (i , p) _ = i , lemma
    where open PosetReasoning ≤-poset

          lemma : 0 ≤ lookup (merge b c) i
          lemma = begin
              0
            ≤⟨ p ⟩
              lookup b i
            ≤⟨ m≤m+n (lookup b i) (lookup c i) ⟩
              lookup b i + lookup c i
            ≈⟨ PE.sym (lookup-zipWith _+_ i b c) ⟩
              lookup (merge b c) i
            ∎

  module _ (A : Model {a} {ℓ}) (n : ℕ) where

    Bag : Set
    Bag = Vec ℕ n

    empty : Bag
    empty = replicate 0

    singleton : Fin n → Bag
    singleton k = updateAt k (λ _ → 1) empty

    singleton-nonempty : ∀ k → NonEmpty (singleton k)
    singleton-nonempty k = k , lemma
      where open PosetReasoning ≤-poset

            lemma : 0 ≤ lookup (singleton k) k
            lemma = begin
                0
              ≤⟨ z≤n ⟩
                1
              ≡⟨ PE.sym (lookup∘updateAt k empty) ⟩
                lookup (singleton k) k
              ∎

    data CSemigroup : Set a where
       sta : Bag → ∥ A ∥ → CSemigroup
       dyn : (x : Bag) → NonEmpty x → CSemigroup

    infix 6 _≋_

    open module A = Setoid ∥ A ∥/≈

    _·_ : ∥ A ∥ → ∥ A ∥ → ∥ A ∥
    x · y = A ⟦ • ⟧ (x ∷ y ∷ [])

    ·-cong : ∀ {x y z w} → x ≈ y → z ≈ w → x · z ≈ y · w
    ·-cong x≈y z≈w = (A ⟦ • ⟧-cong) (x≈y ∷ z≈w ∷ [])

    ·-comm : ∀ (x y : ∥ A ∥) → x · y ≈ y · x
    ·-comm x y = ∥ A ∥ₐ-models comm θ
      where θ : Fin 2 → ∥ A ∥
            θ zero             = x
            θ (suc zero)       = y

    ·-assoc : ∀ (x y z : ∥ A ∥) → (x · y) · z ≈ x · (y · z)
    ·-assoc x y z = ∥ A ∥ₐ-models assoc θ
      where θ : Fin 3 → ∥ A ∥
            θ zero             = x
            θ (suc zero)       = y
            θ (suc (suc zero)) = z

    data _≋_ : CSemigroup → CSemigroup → Set (a ⊔ ℓ) where
      sta : ∀ {b c x y} → b ≡ c → x ≈ y
            → sta b x ≋ sta c y
      dyn : ∀ {b c p q} → b ≡ c → dyn b p ≋ dyn c q

    ≋-refl : ∀ {x} → x ≋ x
    ≋-refl {sta b x} = sta PE.refl A.refl
    ≋-refl {dyn b _} = dyn PE.refl

    ≋-sym : ∀ {x y} → x ≋ y → y ≋ x
    ≋-sym (sta p q) = sta (PE.sym p) (A.sym q)
    ≋-sym (dyn p)   = dyn (PE.sym p)

    ≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
    ≋-trans (sta p q) (sta r s) = sta (PE.trans p r) (A.trans q s)
    ≋-trans (dyn p)   (dyn q)   = dyn (PE.trans p q)

    ≋-isEquivalence : IsEquivalence _≋_
    ≋-isEquivalence = record { refl  = ≋-refl
                             ; sym   = ≋-sym
                             ; trans = ≋-trans
                             }

    ≋-setoid : Setoid a (a ⊔ ℓ)
    ≋-setoid = record { Carrier       = CSemigroup
                      ; _≈_           = _≋_
                      ; isEquivalence = ≋-isEquivalence
                      }

    _++_ : CSemigroup → CSemigroup → CSemigroup
    sta b x ++ sta c y = sta (merge b c) (x · y)
    sta b x ++ dyn c _ = sta (merge b c) x
    dyn b _ ++ sta c y = sta (merge b c) y
    dyn b p ++ dyn c q =
      dyn (merge b c) (merge-preserves {b = b} {c = c} p q)

    ++-comm : ∀ x y → x ++ y ≋ y ++ x
    ++-comm (sta b x) (sta c y) = sta (merge-comm b c) (·-comm x y)
    ++-comm (sta b _) (dyn c _) = sta (merge-comm b c) A.refl
    ++-comm (dyn b _) (sta c _) = sta (merge-comm b c) A.refl
    ++-comm (dyn b _) (dyn c _) = dyn (merge-comm b c)

    ++-assoc : ∀ x y z → (x ++ y) ++ z ≋ x ++ (y ++ z)
    ++-assoc (sta b x) (sta c y) (sta d z) = sta (merge-assoc b c d) (·-assoc x y z)
    ++-assoc (sta b _) (sta c _) (dyn d _) = sta (merge-assoc b c d) A.refl
    ++-assoc (sta b _) (dyn c _) (sta d _) = sta (merge-assoc b c d) A.refl
    ++-assoc (sta b _) (dyn c _) (dyn d _) = sta (merge-assoc b c d) A.refl
    ++-assoc (dyn b _) (sta c _) (sta d _) = sta (merge-assoc b c d) A.refl
    ++-assoc (dyn b _) (sta c _) (dyn d _) = sta (merge-assoc b c d) A.refl
    ++-assoc (dyn b _) (dyn c _) (sta d _) = sta (merge-assoc b c d) A.refl
    ++-assoc (dyn b _) (dyn c _) (dyn d _) = dyn (merge-assoc b c d)

    ++-cong : ∀ {x y z w} → x ≋ y → z ≋ w → x ++ z ≋ y ++ w
    ++-cong (sta b≡c x≈y) (sta d≡e z≈w) = sta (PE.cong₂ merge b≡c d≡e) (·-cong x≈y z≈w)
    ++-cong (sta b≡c x≈y) (dyn d≡e)     = sta (PE.cong₂ merge b≡c d≡e) x≈y
    ++-cong (dyn b≡c)     (sta d≡e z≈w) = sta (PE.cong₂ merge b≡c d≡e) z≈w
    ++-cong (dyn b≡c)     (dyn d≡e)     = dyn (PE.cong₂ merge b≡c d≡e)

    ++-⟦⟧ : Interpretation ≋-setoid
    ++-⟦⟧ • (x ∷ y ∷ []) = x ++ y

    ++-⟦⟧-cong : Congruence ≋-setoid ++-⟦⟧
    ++-⟦⟧-cong • (p ∷ q ∷ []) = ++-cong p q

    ++-isAlgebra : IsAlgebra ≋-setoid
    ++-isAlgebra = record { ⟦_⟧     = ++-⟦⟧
                          ; ⟦⟧-cong = ++-⟦⟧-cong
                          }

    ++-algebra : Algebra
    ++-algebra = record { ∥_∥/≈           = ≋-setoid
                        ; ∥_∥/≈-isAlgebra = ++-isAlgebra
                        }

    ++-models : Models ++-algebra
    ++-models comm θ  = ++-comm (θ (# 0)) (θ (# 1))
    ++-models assoc θ = ++-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

    ++-isModel : IsModel ≋-setoid
    ++-isModel = record { isAlgebra = ++-isAlgebra
                        ; models    = ++-models
                        }

    ++-model : Model
    ++-model = record { ∥_∥/≈   = ≋-setoid
                      ; isModel = ++-isModel
                      }

    ∣inl∣ : ∥ A ∥ → CSemigroup
    ∣inl∣ = sta empty

    ∣inl∣-cong : Congruent ≈[ A ] _≋_ ∣inl∣
    ∣inl∣-cong = sta PE.refl

    ∣inl∣⃗ : ∥ A ∥/≈ ↝ ≋-setoid
    ∣inl∣⃗ = record { ∣_∣      = ∣inl∣
                    ; ∣_∣-cong = ∣inl∣-cong
                    }

    ∣inl∣-hom : Homomorphic ∥ A ∥ₐ ++-algebra ∣inl∣
    ∣inl∣-hom • (x ∷ y ∷ []) = sta (zipWith-identityˡ +-identityˡ empty) A.refl

    inl : ∥ A ∥ₐ ⟿ ++-algebra
    inl = record { ∣_∣⃗    = ∣inl∣⃗
                 ; ∣_∣-hom = ∣inl∣-hom
                 }

    inr : ∥ J n ∥ₐ ⟿ ++-algebra
    inr = interp ++-model (λ k → dyn (singleton k) (singleton-nonempty k))
