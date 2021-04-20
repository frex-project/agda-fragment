{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.Semigroup where

open import Fragment.Equational.Theory.Bundles

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Free Σ-magma hiding (_≑_)
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence; algebra)

open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.Model Θ-semigroup

open import Fragment.Setoid.Morphism using (_↝_)

open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Algebra.Structures using (IsSemigroup)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Fin using (Fin; #_; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)

open import Relation.Nullary using (Dec; yes; no; recompute)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ (A : Model {a} {ℓ}) (n : ℕ) where

  open module A = Setoid ∥ A ∥/≈

  private
    _·_ : ∥ A ∥ → ∥ A ∥ → ∥ A ∥
    x · y = A ⟦ • ⟧ (x ∷ y ∷ [])

    ·-cong : ∀ {x y z w} → x ≈ y → z ≈ w → x · z ≈ y · w
    ·-cong x≈y z≈w = (A ⟦ • ⟧-cong) (x≈y ∷ z≈w ∷ [])

    ·-assoc : ∀ (x y z : ∥ A ∥) → (x · y) · z ≈ x · (y · z)
    ·-assoc x y z = ∥ A ∥ₐ-models assoc θ
      where θ : Fin 3 → ∥ A ∥
            θ zero             = x
            θ (suc zero)       = y
            θ (suc (suc zero)) = z

  data Semigroup : Set a where
    leaf : BT ∥ A ∥ n → Semigroup
    cons : BT ∥ A ∥ n → Semigroup → Semigroup

  pattern leaf₁ x = leaf (sta x)
  pattern leaf₂ x = leaf (dyn x)
  pattern cons₁ x xs = cons (sta x) xs
  pattern cons₂ x ys = cons (dyn x) ys

  open module B = Setoid (Atoms ∥ A ∥/≈ n) renaming (_≈_ to _≑_)

  infix 6 _≋_

  data _≋_ : Semigroup → Semigroup → Set (a ⊔ ℓ) where
    ≈-leaf : ∀ {x y} → x ≑ y → leaf x ≋ leaf y
    ≈-cons : ∀ {x y xs ys} → x ≑ y → xs ≋ ys → cons x xs ≋ cons y ys

  ≋-refl : ∀ {x} → x ≋ x
  ≋-refl {leaf x}    = ≈-leaf B.refl
  ≋-refl {cons x xs} = ≈-cons B.refl ≋-refl

  ≋-sym : ∀ {x y} → x ≋ y → y ≋ x
  ≋-sym (≈-leaf p)   = ≈-leaf (B.sym p)
  ≋-sym (≈-cons p q) = ≈-cons (B.sym p) (≋-sym q)

  ≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
  ≋-trans (≈-leaf p)   (≈-leaf q)   = ≈-leaf (B.trans p q)
  ≋-trans (≈-cons p q) (≈-cons r s) =
    ≈-cons (B.trans p r) (≋-trans q s)

  ≋-isEquivalence : IsEquivalence _≋_
  ≋-isEquivalence = record { refl  = ≋-refl
                           ; sym   = ≋-sym
                           ; trans = ≋-trans
                           }

  ≋-setoid : Setoid a (a ⊔ ℓ)
  ≋-setoid = record { Carrier       = Semigroup
                    ; _≈_           = _≋_
                    ; isEquivalence = ≋-isEquivalence
                    }

  open module S = Setoid ≋-setoid hiding (_≈_)

  consS : ∥ A ∥ → Semigroup → Semigroup
  consS a (leaf₁ x)    = leaf₁ (a · x)
  consS a (cons₁ x xs) = cons₁ (a · x) xs
  consS a x            = cons₁ a x

  consD : Fin n → Semigroup → Semigroup
  consD a x = cons₂ a x

  normalise : Semigroup → Semigroup
  normalise (cons₁ x xs) = consS x (normalise xs)
  normalise (cons₂ x xs) = consD x (normalise xs)
  normalise x            = x

  mutual
    data DNormal : Semigroup → Set a where
      dleaf : ∀ {x} → DNormal (leaf₂ x)
      dhead : ∀ {x xs} → Normal xs → DNormal (cons₂ x xs)

    data SNormal : Semigroup → Set a where
      sleaf : ∀ {x} → SNormal (leaf₁ x)
      shead : ∀ {x ys} → DNormal ys → SNormal (cons₁ x ys)

    data Normal : Semigroup → Set a where
      snorm : ∀ {x} → SNormal x → Normal x
      dnorm : ∀ {x} → DNormal x → Normal x

  pattern Sleaf    = snorm sleaf
  pattern Dleaf    = dnorm dleaf
  pattern SDleaf   = snorm (shead dleaf)
  pattern SDcons p = snorm (shead (dhead p))
  pattern Scons p  = snorm (shead p)
  pattern Dcons p  = dnorm (dhead p)

  normal? : ∀ x → Dec (Normal x)
  normal? (leaf₁ x)              = yes Sleaf
  normal? (leaf₂ x)              = yes Dleaf
  normal? (cons₁ x (leaf₁ y))    = no lemma
    where lemma : ∀ {x y} → Normal (cons₁ x (leaf₁ y)) → ⊥
          lemma (Scons ())
  normal? (cons₁ x (leaf₂ y))    = yes SDleaf
  normal? (cons₁ x (cons₁ y ys)) = no lemma
    where lemma : ∀ {x y xs} → Normal (cons₁ x (cons₁ y xs)) → ⊥
          lemma (Scons ())
  normal? (cons₁ x (cons₂ y ys))
    with normal? ys
  ...  | yes p = yes (SDcons p)
  ...  | no ¬p = no (lemma ¬p)
    where lemma : ∀ {x y xs} → (Normal xs → ⊥) → Normal (cons₁ x (cons₂ y xs)) → ⊥
          lemma ¬p (SDcons q) = ¬p q
  normal? (cons₂ _ xs)
    with normal? xs
  ...  | yes p = yes (Dcons p)
  ...  | no ¬p  = no (lemma ¬p)
    where lemma : ∀ {x xs} → (Normal xs → ⊥) → Normal (cons₂ x xs) → ⊥
          lemma ¬p (Dcons q) = ¬p q

  consS-preserves : ∀ {x xs} → Normal xs → Normal (consS x xs)
  consS-preserves Sleaf      = Sleaf
  consS-preserves SDleaf     = SDleaf
  consS-preserves Dleaf      = SDleaf
  consS-preserves (Dcons p)  = SDcons p
  consS-preserves (SDcons p) = SDcons p

  consS-cong : ∀ {x y xs ys} → x ≈ y → xs ≋ ys
               → consS x xs ≋ consS y ys
  consS-cong x≈y (≈-leaf (sta p))     = ≈-leaf (sta (·-cong x≈y p))
  consS-cong x≈y (≈-cons (sta p) q)   = ≈-cons (sta (·-cong x≈y p)) q
  consS-cong x≈y p@(≈-leaf (dyn _))   = ≈-cons (sta x≈y) p
  consS-cong x≈y p@(≈-cons (dyn _) _) = ≈-cons (sta x≈y) p

  normalise-reduction : ∀ {x} → Normal (normalise x)
  normalise-reduction {x = leaf₁ x}     = Sleaf
  normalise-reduction {x = leaf₂ x}     = Dleaf
  normalise-reduction {x = cons₁ x xs} =
    consS-preserves (normalise-reduction {x = xs})
  normalise-reduction {x = cons₂ x xs} =
    Dcons (normalise-reduction {x = xs})

  _++-raw_ : Semigroup → Semigroup → Semigroup
  leaf₁ x    ++-raw y = consS x y
  leaf₂ x    ++-raw y = consD x y
  cons₁ x xs ++-raw y = consS x (xs ++-raw y)
  cons₂ x xs ++-raw y = consD x (xs ++-raw y)

  ++-raw-cong : ∀ {x y z w} → x ≋ y → z ≋ w
                → x ++-raw z ≋ y ++-raw w
  ++-raw-cong (≈-leaf (sta p)) q   = consS-cong p q
  ++-raw-cong (≈-leaf (dyn p)) q   = ≈-cons (dyn p) q
  ++-raw-cong (≈-cons (sta p) q) r = consS-cong p (++-raw-cong q r)
  ++-raw-cong (≈-cons (dyn p) q) r = ≈-cons (dyn p) (++-raw-cong q r)

  consS-· : ∀ {a b} → (x : Semigroup) → consS (a · b) x ≋ consS a (consS b x)
  consS-· {a = a} {b = b} (leaf₁ x)    = ≈-leaf (sta (·-assoc a b x))
  consS-· {a = a} {b = b} (cons₁ x xs) = ≈-cons (sta (·-assoc a b x)) S.refl
  consS-· (leaf₂ x)                    = S.refl
  consS-· (cons₂ x xs)                 = S.refl

  consS-++ : ∀ {a} → (x y : Semigroup)
             → (consS a x) ++-raw y ≋ consS a (x ++-raw y)
  consS-++ {a = a} (leaf₁ x) (leaf₁ y)    = ≈-leaf (sta (·-assoc a x y))
  consS-++ {a = a} (leaf₁ x) (cons₁ y ys) = ≈-cons (sta (·-assoc a x y)) S.refl
  consS-++ (leaf₁ x) (leaf₂ y)            = S.refl
  consS-++ (leaf₁ x) (cons₂ y ys)         = S.refl
  consS-++ (leaf₂ x) y                    = S.refl
  consS-++ (cons₂ x xs) y                 = S.refl
  consS-++ {a = a} (cons₁ x xs) y         = begin
      (consS a (cons₁ x xs)) ++-raw y
    ≈⟨ ++-raw-cong (S.refl {x = cons₁ (a · x) xs}) S.refl ⟩
      (cons₁ (a · x) xs) ++-raw y
    ≡⟨⟩
      consS (a · x) (xs ++-raw y)
    ≈⟨ consS-· (xs ++-raw y) ⟩
      consS a ((cons₁ x xs) ++-raw y)
    ∎
    where open import Relation.Binary.Reasoning.Setoid ≋-setoid

  ++-raw-assoc : ∀ (x y z : Semigroup)
                 → (x ++-raw y) ++-raw z ≋ x ++-raw (y ++-raw z)
  ++-raw-assoc (leaf₁ x) (leaf₁ y) (leaf₂ z) = S.refl
  ++-raw-assoc (leaf₁ x) (leaf₂ y) z         = S.refl
  ++-raw-assoc (leaf₂ x) y z                 = S.refl
  ++-raw-assoc (leaf₁ x) y z                 = consS-++ y z
  ++-raw-assoc (cons₂ x xs) y z              =
    ≈-cons B.refl (++-raw-assoc xs y z)
  ++-raw-assoc (cons₁ x xs) y z              = begin
      (consS x (xs ++-raw y)) ++-raw z
    ≈⟨ consS-++ (xs ++-raw y) z ⟩
      consS x ((xs ++-raw y) ++-raw z)
    ≈⟨ consS-cong A.refl (++-raw-assoc xs y z) ⟩
      consS x (xs ++-raw (y ++-raw z))
    ∎
    where open import Relation.Binary.Reasoning.Setoid ≋-setoid

  _++ₙ_ : ∀ {x y} →  Normal x → Normal y → Normal (x ++-raw y)
  _++ₙ_ Sleaf q      = consS-preserves q
  _++ₙ_ Dleaf q      = Dcons q
  _++ₙ_ SDleaf q     = SDcons q
  _++ₙ_ (Dcons p) q  = Dcons (p ++ₙ q)
  _++ₙ_ (SDcons p) q = SDcons (p ++ₙ q)

  ++-D : ∀ {x y : Semigroup}
         → DNormal x
         → Normal y
         → DNormal (x ++-raw y)
  ++-D dleaf q     = dhead q
  ++-D (dhead p) q = dhead (p ++ₙ q)

  consSD-lemma : ∀ {x y} → DNormal y → cons₁ x y ≡ consS x y
  consSD-lemma dleaf     = PE.refl
  consSD-lemma (dhead x) = PE.refl

  record NormalSemigroup : Set a where
    constructor _,_
    field
      x       : Semigroup
      .normal : Normal x

  infix 6 _~_

  _~_ : NormalSemigroup → NormalSemigroup → Set (a ⊔ ℓ)
  (x , _) ~ (y , _) = x ≋ y

  ~-isEquivalence : IsEquivalence _~_
  ~-isEquivalence = record { refl  = ≋-refl
                           ; sym   = ≋-sym
                           ; trans = ≋-trans
                           }

  ~-setoid : Setoid a (a ⊔ ℓ)
  ~-setoid = record { Carrier       = NormalSemigroup
                    ; _≈_           = _~_
                    ; isEquivalence = ~-isEquivalence
                    }

  open module N = Setoid ~-setoid hiding (_≈_)

  _++_ : NormalSemigroup → NormalSemigroup → NormalSemigroup
  (x , p) ++ (y , q) = x ++-raw y , p ++ₙ q

  ++-assoc : ∀ (x y z : NormalSemigroup)
             → (x ++ y) ++ z ~ x ++ (y ++ z)
  ++-assoc (x , _) (y , _) (z , _) = ++-raw-assoc x y z

  ++-⟦_⟧ : Interpretation ~-setoid
  ++-⟦ • ⟧ (x ∷ y ∷ []) = x ++ y

  ++-⟦⟧-cong : Congruence ~-setoid ++-⟦_⟧
  ++-⟦⟧-cong • (x≋y ∷ z≋w ∷ []) = ++-raw-cong x≋y z≋w

  ++-isAlgebra : IsAlgebra ~-setoid
  ++-isAlgebra = record { ⟦_⟧     = ++-⟦_⟧
                        ; ⟦⟧-cong = ++-⟦⟧-cong
                        }

  ++-algebra : Algebra
  ++-algebra = algebra ~-setoid ++-isAlgebra

  ++-models : Models ++-algebra
  ++-models assoc θ = ++-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

  ++-isModel : IsModel ~-setoid
  ++-isModel = record { isAlgebra = ++-isAlgebra
                      ; models    = ++-models
                      }

  ++-model : Model
  ++-model = record { ∥_∥/≈   = ~-setoid
                    ; isModel = ++-isModel
                    }

  ∣inl∣ : ∥ A ∥ → NormalSemigroup
  ∣inl∣ a = leaf₁ a , Sleaf

  ∣inl∣-cong : Congruent _≈_ _~_ ∣inl∣
  ∣inl∣-cong = ≈-leaf ∘ sta

  ∣inl∣⃗ : ∥ A ∥/≈ ↝ ~-setoid
  ∣inl∣⃗ = record { ∣_∣ = ∣inl∣
                  ; ∣_∣-cong = ∣inl∣-cong
                  }

  ∣inl∣-hom : Homomorphic ∥ A ∥ₐ ++-algebra ∣inl∣
  ∣inl∣-hom • (x ∷ y ∷ []) = N.refl {x = _ , Sleaf}

  inl : ∥ A ∥ₐ ⟿ ++-algebra
  inl = record { ∣_∣⃗    = ∣inl∣⃗
               ; ∣_∣-hom = ∣inl∣-hom
               }

  inr-θ : Env ++-algebra n
  inr-θ k = leaf₂ k , Dleaf

  inr : ∥ J n ∥ₐ ⟿ ++-algebra
  inr = interp ++-model inr-θ

  module _ {b ℓ} (X : Model {b} {ℓ}) where

    open module X = Setoid ∥ X ∥/≈ renaming (_≈_ to _≐_)

    private
      _⊕_ : ∥ X ∥ → ∥ X ∥ → ∥ X ∥
      x ⊕ y = X ⟦ • ⟧ (x ∷ y ∷ [])

      ⊕-cong : ∀ {x y z w} → x ≐ y → z ≐ w → x ⊕ z ≐ y ⊕ w
      ⊕-cong p q = (X ⟦ • ⟧-cong) (p ∷ q ∷ [])

      ⊕-assoc : ∀ (x y z : ∥ X ∥) → (x ⊕ y) ⊕ z ≐ x ⊕ (y ⊕ z)
      ⊕-assoc x y z = ∥ X ∥ₐ-models assoc θ
        where θ : Fin 3 → ∥ X ∥
              θ zero             = x
              θ (suc zero)       = y
              θ (suc (suc zero)) = z

    module _
      {f : ∥ A ∥ₐ ⟿ ∥ X ∥ₐ}
      {g : ∥ J n ∥ₐ ⟿ ∥ X ∥ₐ}
      where

      ∣base∣ = ∣sub∣ ∥ X ∥/≈ ∣ f ∣⃗ (λ k → ∣ g ∣ (atom (dyn k)))
      ∣base∣-cong = ∣sub∣-cong ∥ X ∥/≈ ∣ f ∣⃗ (λ k → ∣ g ∣ (atom (dyn k)))

      ++-[_,_]-raw : Semigroup → ∥ X ∥
      ++-[_,_]-raw (leaf x)    = ∣base∣ x
      ++-[_,_]-raw (cons x xs) = ∣base∣ x ⊕ ++-[_,_]-raw xs

      ++-[_,_] : NormalSemigroup → ∥ X ∥
      ++-[_,_] (x , _) = ++-[_,_]-raw x

      ++-[_,_]-raw-cong : Congruent _≋_ _≐_ ++-[_,_]-raw
      ++-[_,_]-raw-cong (≈-leaf p)   = ∣base∣-cong p
      ++-[_,_]-raw-cong (≈-cons p q) =
        ⊕-cong (∣base∣-cong p) (++-[_,_]-raw-cong q)

      open import Relation.Binary.Reasoning.Setoid ∥ X ∥/≈

      ++-[_,_]-raw-hom : ∀ (x y : Σ[ x ∈ Semigroup ] (Normal x))
                         → (++-[_,_]-raw (proj₁ x) ⊕ ++-[_,_]-raw (proj₁ y))
                            ≐ ++-[_,_]-raw (proj₁ x ++-raw proj₁ y)
      ++-[_,_]-raw-hom (leaf₁ x , _) (leaf₁ y , _)   = ∣ f ∣-hom • (x ∷ y ∷ [])
      ++-[_,_]-raw-hom (leaf₁ _ , _) (leaf₂ _ , _)   = X.refl
      ++-[_,_]-raw-hom (leaf₁ x , _) (cons₁ y z , _) = begin
          ∣ f ∣ x ⊕ (∣ f ∣ y ⊕ ++-[_,_]-raw z)
        ≈⟨ X.sym (⊕-assoc (∣ f ∣ x) (∣ f ∣ y) (++-[_,_]-raw z)) ⟩
          (∣ f ∣ x ⊕ ∣ f ∣ y) ⊕ ++-[_,_]-raw z
        ≈⟨ ⊕-cong (∣ f ∣-hom • (x ∷ y ∷ [])) X.refl ⟩
          ∣ f ∣ (x · y) ⊕ ++-[_,_]-raw z
        ∎
      ++-[_,_]-raw-hom (leaf₁ x , _) (cons₂ _ _ , _) = ⊕-cong X.refl X.refl
      ++-[_,_]-raw-hom (leaf₂ _ , _) _               = X.refl
      ++-[_,_]-raw-hom (cons₁ x y , Scons q) (z , r) = begin
          (∣ f ∣ x ⊕ ++-[_,_]-raw y) ⊕ ++-[_,_] (z , r)
        ≈⟨ ⊕-assoc (∣ f ∣ x) (++-[_,_]-raw y) (++-[_,_] (z , r)) ⟩
          ∣ f ∣ x ⊕ (++-[_,_]-raw y ⊕ ++-[_,_] (z , r))
        ≈⟨ ⊕-cong X.refl (++-[_,_]-raw-hom (y , dnorm q) (z , r)) ⟩
          ∣ f ∣ x ⊕ ++-[_,_] ((y , dnorm q) ++ (z , r))
        ≈⟨ ++-[_,_]-raw-cong (S.reflexive (consSD-lemma (++-D q (recompute (normal? z) r)))) ⟩
          ++-[_,_]-raw (consS x (y ++-raw z))
        ≈⟨ X.sym (++-[_,_]-raw-cong (consS-++ {a = x} y z)) ⟩
          ++-[_,_]-raw ((consS x y) ++-raw z)
        ≈⟨ X.sym (++-[_,_]-raw-cong (++-raw-cong (S.reflexive (consSD-lemma q)) S.refl)) ⟩
          ++-[_,_]-raw ((cons₁ x y) ++-raw z)
        ∎
      ++-[_,_]-raw-hom (cons₂ x xs , Dcons p) (y , q)       = begin
          (∣ g ∣ (atom (dyn x)) ⊕ ++-[_,_]-raw xs) ⊕ ++-[_,_]-raw y
        ≈⟨ ⊕-assoc (∣ g ∣ (atom (dyn x))) (++-[_,_]-raw xs) (++-[_,_]-raw y) ⟩
          ∣ g ∣ (atom (dyn x)) ⊕ (++-[_,_]-raw xs ⊕ ++-[_,_]-raw y)
        ≈⟨ ⊕-cong X.refl (++-[_,_]-raw-hom (xs , p) (y , q)) ⟩
          ∣ g ∣ (atom (dyn x)) ⊕ ++-[_,_]-raw (xs ++-raw y)
        ∎

      ++-[_,_]-hom : ∀ (x y : NormalSemigroup)
                     → (++-[_,_] x ⊕ ++-[_,_] y) ≐ ++-[_,_] (x ++ y)
      ++-[_,_]-hom (x , p) (y , q)
        with recompute (normal? x) p
           | recompute (normal? y) q
      ...  | r | s  = ++-[_,_]-raw-hom (x , r) (y , s)

      _[_,_] : ++-algebra ⟿ ∥ X ∥ₐ
      _[_,_] = record { ∣_∣⃗      = record { ∣_∣ = ++-[_,_] ; ∣_∣-cong = ++-[_,_]-raw-cong }
                      ; ∣_∣-hom  = hom
                      }
        where hom : Homomorphic ++-algebra ∥ X ∥ₐ ++-[_,_]
              hom • (x ∷ y ∷ []) = ++-[_,_]-hom x y

      commute₁ : _[_,_] ⊙ inl ≗ f
      commute₁ = X.refl

      commute₂ : _[_,_] ⊙ inr ≗ g
      commute₂ {x = atom (dyn k)} =
        ++-[_,_]-raw-cong (S.refl {x = leaf₂ k})
      commute₂ {x = t@(term • (x ∷ y ∷ []))} = begin
          ++-[_,_] (∣ inr ∣ t)
        ≈⟨ ++-[_,_]-raw-cong (∣ inr ∣-hom • (x ∷ y ∷ [])) ⟩
          ++-[_,_] (subst-x ++ subst-y)
        ≈⟨ X.sym (++-[_,_]-hom subst-x subst-y) ⟩
          (++-[_,_] subst-x) ⊕ (++-[_,_] subst-y)
        ≈⟨ ⊕-cong commute₂ commute₂ ⟩
          ∣ g ∣ x ⊕ ∣ g ∣ y
        ≈⟨ ∣ g ∣-hom • (x ∷ y ∷ []) ⟩
          ∣ g ∣ t
        ∎
        where subst-x = ∣ interp ++-model inr-θ ∣ x
              subst-y = ∣ interp ++-model inr-θ ∣ y

      module _ {h : ++-algebra ⟿ ∥ X ∥ₐ} where

        ++-[_,_]-raw-universal : h ⊙ inl ≗ f → h ⊙ inr ≗ g
                                 → ∀ {x : Σ[ x ∈ Semigroup ] (Normal x)}
                                 → ++-[_,_] (proj₁ x , proj₂ x) ≐ ∣ h ∣ (proj₁ x , proj₂ x)
        ++-[_,_]-raw-universal c₁ c₂ {leaf₁ x , _} = X.sym c₁
        ++-[_,_]-raw-universal c₁ c₂ {leaf₂ x , _} = X.sym c₂
        ++-[_,_]-raw-universal c₁ c₂ {cons₁ x y , Scons p} = begin
            ∣ f ∣ x ⊕ ++-[_,_] (y , dnorm p)
          ≈⟨ ⊕-cong (X.sym c₁) (++-[_,_]-raw-universal c₁ c₂ {y , dnorm p}) ⟩
            ∣ h ∣ (leaf₁ x , _) ⊕ ∣ h ∣ (y , dnorm p)
          ≈⟨ ∣ h ∣-hom • ((leaf₁ x , _) ∷ (y , dnorm p) ∷ []) ⟩
            ∣ h ∣ (consS x y , consS-preserves (dnorm p))
          ≈⟨ X.sym (∣ h ∣-cong (S.reflexive (consSD-lemma p))) ⟩
            ∣ h ∣ (cons₁ x y , Scons p)
          ∎
        ++-[_,_]-raw-universal c₁ c₂ {cons₂ x y , Dcons q} = begin
            ∣ g ∣ (atom (dyn x)) ⊕ ++-[_,_] (y , q)
          ≈⟨ ⊕-cong (X.sym c₂) (++-[_,_]-raw-universal c₁ c₂ {x = (y , q)}) ⟩
            ∣ h ∣ (leaf₂ x , _) ⊕ ∣ h ∣ (y , q)
          ≈⟨ ∣ h ∣-hom • ((leaf₂ x , _) ∷ (y , q) ∷ []) ⟩
            ∣ h ∣ ((leaf₂ x , Dleaf) ++ (y , q))
          ∎

        ++-[_,_]-universal : h ⊙ inl ≗ f → h ⊙ inr ≗ g → _[_,_] ≗ h
        ++-[_,_]-universal c₁ c₂ {x = x , p}
          with recompute (normal? x) p
        ...  | q = ++-[_,_]-raw-universal c₁ c₂ {x = x , q}

++-model-isFrex : IsFreeExtension ++-model
++-model-isFrex A n =
  record { inl       = inl A n
         ; inr       = inr A n
         ; _[_,_]    = λ X → λ f → λ g → _[_,_] A n X {f = f} {g = g}
         ; commute₁  = λ {_} {_} {X} {f} {g} → commute₁ A n X {f = f} {g = g}
         ; commute₂  = λ {_} {_} {X} {f} {g} → commute₂ A n X {f = f} {g = g}
         ; universal = λ {_} {_} {X} {f} {g} {h} → ++-[_,_]-universal A n X {f = f} {g = g} {h = h}
         }

SemigroupFrex : FreeExtension
SemigroupFrex = record { _[_]        = ++-model
                       ; _[_]-isFrex = ++-model-isFrex
                       }
