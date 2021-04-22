{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.CSemigroup where

open import Fragment.Equational.Theory.Bundles

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Free Σ-magma hiding (_~_)
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence)

open import Fragment.Equational.FreeExtension Θ-csemigroup
open import Fragment.Equational.Model Θ-csemigroup

open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level; _⊔_)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityˡ)
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Vec using (Vec; []; _∷_; zipWith; lookup; replicate; updateAt; tabulate)
open import Data.Vec.Properties
  using (lookup-zipWith; zipWith-comm; zipWith-assoc; zipWith-identityˡ; lookup∘updateAt; lookup∘tabulate)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

open import Relation.Nullary using (Dec; yes; no; recompute)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
import Relation.Binary.Reasoning.Setoid as Reasoning

private
  variable
    a ℓ : Level

  NonEmpty : ∀ {n} → Vec ℕ n → Set
  NonEmpty {n} xs = Σ[ i ∈ Fin n ] Σ[ k ∈ ℕ ] (lookup xs i ≡ suc k)

  nonempty? : ∀ {n} → (x : Vec ℕ n) → Dec (NonEmpty x)
  nonempty? []           = no λ ()
  nonempty? (zero ∷ xs)
    with nonempty? xs
  ...  | yes (i , p) = yes (suc i , p)
  ...  | no ¬p       = no lemma
    where lemma : NonEmpty (zero ∷ xs) → ⊥
          lemma (suc i , p) = ¬p (i , p)
  nonempty? (suc x ∷ xs) = yes (zero , x , PE.refl)

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
  merge-preserves {b = b} {c = c} (i , n , p) _ =
    i , n + lookup c i , lemma
    where open PE.≡-Reasoning

          lemma : lookup (merge b c) i ≡ suc (n + lookup c i)
          lemma = begin
              lookup (merge b c) i
            ≡⟨ lookup-zipWith _+_ i b c ⟩
              lookup b i + lookup c i
            ≡⟨ PE.cong (_+ lookup c i) p ⟩
              suc n + lookup c i
            ∎

  expand : ∀ {a n} {A : Set a} → (A → A → A)
           → Vec A n → Vec ℕ n → Maybe A
  expand f []       []           = nothing
  expand f (x ∷ xs) (zero ∷ ks)  = expand f xs ks
  expand f (x ∷ xs) (suc k ∷ ks)
    with expand f (x ∷ xs) (k ∷ ks)
  ...  | just x' = just (f x x')
  ...  | nothing = just x

  ∷-nonempty : ∀ {n x} {xs : Vec ℕ n}
               → NonEmpty xs → NonEmpty (x ∷ xs)
  ∷-nonempty (i , n , p) = suc i , n , p

  zero-nonempty : ∀ {n} {xs : Vec ℕ n}
                  → NonEmpty (zero ∷ xs) → NonEmpty xs
  zero-nonempty (suc i , n , p) = i , n , p

  expand-empty : ∀ {a n} {A : Set a}
                 → {f : A → A → A}
                 → {xs : Vec A n}
                 → expand f xs (replicate 0) ≡ nothing
  expand-empty {xs = []}     = PE.refl
  expand-empty {xs = x ∷ xs} = expand-empty {xs = xs}

  force : ∀ {a n} {A : Set a}
          → (f : A → A → A)
          → (xs : Vec A n)
          → (ks : Vec ℕ n)
          → .(NonEmpty ks)
          → Σ[ x ∈ A ] (expand f xs ks ≡ just x)
  force f (x ∷ xs) (zero ∷ ks)  p
    = force f xs ks (zero-nonempty p)
  force f (x ∷ xs) (suc k ∷ ks) p
    with expand f (x ∷ xs) (k ∷ ks)
  ...  | just x' = f x x' , PE.refl
  ...  | nothing = x , PE.refl

  empty : ∀ {n} → Vec ℕ n
  empty = replicate 0

  singleton : ∀ {n} → Fin n → Vec ℕ n
  singleton k = updateAt k (λ _ → 1) empty

  singleton-nonempty : ∀ {n} → (k : Fin n) → NonEmpty (singleton {n} k)
  singleton-nonempty k = k , 0 , lookup∘updateAt k empty

  singleton-force : ∀ {a n} {A : Set a}
                    → (f : A → A → A)
                    → (xs : Vec A n)
                    → (k : Fin n)
                    → expand f xs (singleton k) ≡ just (lookup xs k)
  singleton-force f (x ∷ xs) zero
    with expand f xs empty | expand-empty {f = f} {xs}
  ...  | nothing           | _ = PE.refl
  singleton-force f (x ∷ xs) (suc k) = singleton-force f xs k

  module _ (A : Model {a} {ℓ}) (n : ℕ) where

    Bag : Set
    Bag = Vec ℕ n

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

    module _ {b ℓ} (X : Model {b} {ℓ}) where

      private

        open module X = Setoid ∥ X ∥/≈ renaming (_≈_ to _~_)

        _⊕_ : ∥ X ∥ → ∥ X ∥ → ∥ X ∥
        x ⊕ y = X ⟦ • ⟧ (x ∷ y ∷ [])

        ⊕-cong : ∀ {x y z w} → x ~ y → z ~ w → x ⊕ z ~ y ⊕ w
        ⊕-cong p q = (X ⟦ • ⟧-cong) (p ∷ q ∷ [])

        ⊕-comm : ∀ (x y : ∥ X ∥) → x ⊕ y ~ y ⊕ x
        ⊕-comm x y = ∥ X ∥ₐ-models comm θ
          where θ : Fin 2 → ∥ X ∥
                θ zero             = x
                θ (suc zero)       = y

        ⊕-assoc : ∀ (x y z : ∥ X ∥) → (x ⊕ y) ⊕ z ~ x ⊕ (y ⊕ z)
        ⊕-assoc x y z = ∥ X ∥ₐ-models assoc θ
          where θ : Fin 3 → ∥ X ∥
                θ zero             = x
                θ (suc zero)       = y
                θ (suc (suc zero)) = z

      module _
        (f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ)
        (g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ)
        where

        private

          env : Vec ∥ X ∥ n
          env = tabulate (λ k → ∣ g ∣ (atom (dyn k)))

        ∣resid∣ : CSemigroup → ∥ X ∥
        ∣resid∣ (sta b x)
          with expand _⊕_ env b
        ...  | just x' = ∣ f ∣ x ⊕ x'
        ...  | nothing = ∣ f ∣ x
        ∣resid∣ (dyn b p) = proj₁ (force _⊕_ env b p)

        ∣resid∣-cong : Congruent _≋_ _~_ ∣resid∣
        ∣resid∣-cong (sta {b} PE.refl q)
          with expand _⊕_ env b
        ...  | just x' = ⊕-cong (∣ f ∣-cong q) X.refl
        ...  | nothing = ∣ f ∣-cong q
        ∣resid∣-cong (dyn PE.refl) = X.refl

        ∣resid∣⃗ : ≋-setoid ↝ ∥ X ∥/≈
        ∣resid∣⃗ = record { ∣_∣      = ∣resid∣
                          ; ∣_∣-cong = ∣resid∣-cong
                          }

        open Reasoning ∥ X ∥/≈

        ∣resid∣-hom : Homomorphic ++-algebra ∥ X ∥ₐ ∣resid∣
        ∣resid∣-hom • (sta b x ∷ sta c y ∷ []) = {!!}
        ∣resid∣-hom • (sta b x ∷ dyn c q ∷ []) = {!!}
        ∣resid∣-hom • (dyn b p ∷ sta c y ∷ []) = {!!}
        ∣resid∣-hom • (dyn b p ∷ dyn c q ∷ []) = {!!}

        _[_,_] : ++-algebra ⟿ ∥ X ∥ₐ
        _[_,_] = record { ∣_∣⃗    = ∣resid∣⃗
                        ; ∣_∣-hom = ∣resid∣-hom
                        }
    module _
      {b ℓ} {X : Model {b} {ℓ}}
      {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
      {g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ}
      where

      private

        open module X = Setoid ∥ X ∥/≈ renaming (_≈_ to _~_)

        _⊕_ : ∥ X ∥ → ∥ X ∥ → ∥ X ∥
        x ⊕ y = X ⟦ • ⟧ (x ∷ y ∷ [])

        ⊕-cong : ∀ {x y z w} → x ~ y → z ~ w → x ⊕ z ~ y ⊕ w
        ⊕-cong p q = (X ⟦ • ⟧-cong) (p ∷ q ∷ [])

        env : Vec ∥ X ∥ n
        env = tabulate (λ k → ∣ g ∣ (atom (dyn k)))

      open Reasoning ∥ X ∥/≈

      commute₁ : X [ f , g ] ⊙ inl ≗ f
      commute₁ {x}
        with expand _⊕_ env empty
           | expand-empty {f = _⊕_} {xs = env}
      ...  | nothing | _ = X.refl

      commute₂ : X [ f , g ] ⊙ inr ≗ g
      commute₂ {t@(atom (dyn k))}
        with force _⊕_ env (singleton k) (singleton-nonempty k)
      ...  | (x , p) = begin
          x
        ≡⟨ just-injective (PE.trans (PE.sym p) (singleton-force _⊕_ env k)) ⟩
          lookup env k
        ≡⟨ lookup∘tabulate (λ k → ∣ g ∣ (atom (dyn k))) k ⟩
          ∣ g ∣ (atom (dyn k))
        ∎
      commute₂ {t@(term • (x ∷ y ∷ []))} = begin
          ∣ X [ f , g ] ∣ (∣ inr ∣ t)
        ≈⟨ ∣ X [ f , g ] ∣-cong (≋-sym (∣ inr ∣-hom • (x ∷ y ∷ []))) ⟩
          ∣ X [ f , g ] ∣ (∣ inr ∣ x ++ ∣ inr ∣ y)
        ≈⟨ X.sym (∣ X [ f , g ] ∣-hom • (∣ inr ∣ x ∷ ∣ inr ∣ y ∷ [])) ⟩
          ∣ X [ f , g ] ∣ (∣ inr ∣ x) ⊕ ∣ X [ f , g ] ∣ (∣ inr ∣ y)
        ≈⟨ ⊕-cong commute₂ commute₂ ⟩
          ∣ g ∣ x ⊕ ∣ g ∣ y
        ≈⟨ ∣ g ∣-hom • (x ∷ y ∷ []) ⟩
          ∣ g ∣ t
        ∎

      module _ {h : ++-algebra ⟿ ∥ X ∥ₐ}
        (c₁ : h ⊙ inl ≗ f)
        (c₂ : h ⊙ inr ≗ g)
        where

        universal : X [ f , g ] ≗ h
        universal = {!!}

private

  ++-model-isFrex : IsFreeExtension ++-model
  ++-model-isFrex A n =
    record { inl       = inl A n
           ; inr       = inr A n
           ; _[_,_]    = _[_,_] A n
           ; commute₁  = λ {_ _ X f g} → commute₁ A n {X = X} {f} {g}
           ; commute₂  = λ {_ _ X f g} → commute₂ A n {X = X} {f} {g}
           ; universal = λ {_ _ X f g h} → universal A n {X = X} {f} {g} {h}
           }

CSemigroupFrex : FreeExtension
CSemigroupFrex = record { _[_]        = ++-model
                        ; _[_]-isFrex = ++-model-isFrex
                        }
