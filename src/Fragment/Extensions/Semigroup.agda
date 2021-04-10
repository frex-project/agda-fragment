{-# OPTIONS --without-K --safe #-}

module Fragment.Extensions.Semigroup where

open import Fragment.Equational.Theory.Bundles

open import Fragment.Algebra.Signature
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Homomorphism.Setoid Σ-magma
open import Fragment.Algebra.FreeAlgebra Σ-magma using (subst; term₁; term₂)
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence; algebra)

open import Fragment.Extensions.Base hiding (_≈BT_)

open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.FreeModel Θ-semigroup
open import Fragment.Equational.Model Θ-semigroup

open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Algebra.Structures using (IsSemigroup)

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Fin using (Fin; #_; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)

open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

private
  variable
    a ℓ : Level

module _ (M : Model {a} {ℓ}) (n : ℕ) where

  open module M = Setoid ∥ M ∥/≈ using (_≈_)
  open module T = Setoid ∥ |T|⦉ n ⦊/≈ₘ ∥/≈ renaming (_≈_ to _≈ₘ_)
  open module B = Setoid (≈BT-setoid n ∥ M ∥/≈) renaming (_≈_ to _≈BT_)

  open import Fragment.Algebra.TermAlgebra (Σ-magma ⦉ n ⦊)

  private
    _·_ : ∥ M ∥ → ∥ M ∥ → ∥ M ∥
    x · y = (M ⟦ • ⟧) (x ∷ y ∷ [])

    ·-cong : ∀ {x y z w} → x ≈ y → z ≈ w → x · z ≈ y · w
    ·-cong x≈y z≈w = (M ⟦⟧-cong) • (x≈y ∷ z≈w ∷ [])

    ·-assoc : ∀ (x y z : ∥ M ∥) → (x · y) · z ≈ x · (y · z)
    ·-assoc x y z = ∥ M ∥ₐ-models assoc {θ = θ}
      where θ : Fin 3 → ∥ M ∥
            θ zero             = x
            θ (suc zero)       = y
            θ (suc (suc zero)) = z

  data Semigroup : Set a where
    leaf : BT n ∥ M ∥ → Semigroup
    cons : BT n ∥ M ∥ → Semigroup → Semigroup

  pattern leaf₁ x = leaf (sta x)
  pattern leaf₂ x = leaf (dyn x)
  pattern cons₁ x xs = cons (sta x) xs
  pattern cons₂ x ys = cons (dyn x) ys

  infix 6 _≈ₛ_

  data _≈ₛ_ : Semigroup → Semigroup → Set (a ⊔ ℓ) where
    ≈-leaf : ∀ {x y} → x ≈BT y → leaf x ≈ₛ leaf y
    ≈-cons : ∀ {x y xs ys} → x ≈BT y → xs ≈ₛ ys → cons x xs ≈ₛ cons y ys

  ≈ₛ-refl : ∀ {x} → x ≈ₛ x
  ≈ₛ-refl {leaf x}    = ≈-leaf B.refl
  ≈ₛ-refl {cons x xs} = ≈-cons B.refl ≈ₛ-refl

  ≈ₛ-sym : ∀ {x y} → x ≈ₛ y → y ≈ₛ x
  ≈ₛ-sym (≈-leaf p)   = ≈-leaf (B.sym p)
  ≈ₛ-sym (≈-cons p q) = ≈-cons (B.sym p) (≈ₛ-sym q)

  ≈ₛ-trans : ∀ {x y z} → x ≈ₛ y → y ≈ₛ z → x ≈ₛ z
  ≈ₛ-trans (≈-leaf p)   (≈-leaf q)   = ≈-leaf (B.trans p q)
  ≈ₛ-trans (≈-cons p q) (≈-cons r s) =
    ≈-cons (B.trans p r) (≈ₛ-trans q s)

  ≈ₛ-isEquivalence : IsEquivalence _≈ₛ_
  ≈ₛ-isEquivalence = record { refl  = ≈ₛ-refl
                            ; sym   = ≈ₛ-sym
                            ; trans = ≈ₛ-trans
                            }

  ≈ₛ-setoid : Setoid a (a ⊔ ℓ)
  ≈ₛ-setoid = record { Carrier       = Semigroup
                     ; _≈_           = _≈ₛ_
                     ; isEquivalence = ≈ₛ-isEquivalence
                     }

  open module S = Setoid ≈ₛ-setoid hiding (_≈_)

  consS : ∥ M ∥ → Semigroup → Semigroup
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

  consS-preserves : ∀ {x xs} → Normal xs → Normal (consS x xs)
  consS-preserves Sleaf      = Sleaf
  consS-preserves SDleaf     = SDleaf
  consS-preserves Dleaf      = SDleaf
  consS-preserves (Dcons p)  = SDcons p
  consS-preserves (SDcons p) = SDcons p

  consS-cong : ∀ {x y xs ys} → x ≈ y → xs ≈ₛ ys
               → consS x xs ≈ₛ consS y ys
  consS-cong x≈y (≈-leaf (≈-sta p))     = ≈-leaf (≈-sta (·-cong x≈y p))
  consS-cong x≈y (≈-cons (≈-sta p) q)   = ≈-cons (≈-sta (·-cong x≈y p)) q
  consS-cong x≈y p@(≈-leaf (≡-dyn _))   = ≈-cons (≈-sta x≈y) p
  consS-cong x≈y p@(≈-cons (≡-dyn _) _) = ≈-cons (≈-sta x≈y) p

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

  ++-raw-cong : ∀ {x y z w} → x ≈ₛ y → z ≈ₛ w
                → x ++-raw z ≈ₛ y ++-raw w
  ++-raw-cong (≈-leaf (≈-sta p)) q   = consS-cong p q
  ++-raw-cong (≈-leaf (≡-dyn p)) q   = ≈-cons (≡-dyn p) q
  ++-raw-cong (≈-cons (≈-sta p) q) r = consS-cong p (++-raw-cong q r)
  ++-raw-cong (≈-cons (≡-dyn p) q) r = ≈-cons (≡-dyn p) (++-raw-cong q r)

  consS-· : ∀ {a b} → (x : Semigroup) → consS (a · b) x ≈ₛ consS a (consS b x)
  consS-· {a = a} {b = b} (leaf₁ x)    = ≈-leaf (≈-sta (·-assoc a b x))
  consS-· {a = a} {b = b} (cons₁ x xs) = ≈-cons (≈-sta (·-assoc a b x)) S.refl
  consS-· (leaf₂ x)                    = S.refl
  consS-· (cons₂ x xs)                 = S.refl

  consS-++ : ∀ {a} → (x y : Semigroup)
             → (consS a x) ++-raw y ≈ₛ consS a (x ++-raw y)
  consS-++ {a = a} (leaf₁ x) (leaf₁ y)    = ≈-leaf (≈-sta (·-assoc a x y))
  consS-++ {a = a} (leaf₁ x) (cons₁ y ys) = ≈-cons (≈-sta (·-assoc a x y)) S.refl
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
    where open import Relation.Binary.Reasoning.Setoid ≈ₛ-setoid

  ++-raw-assoc : ∀ (x y z : Semigroup)
                 → (x ++-raw y) ++-raw z ≈ₛ x ++-raw (y ++-raw z)
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
    ≈⟨ consS-cong M.refl (++-raw-assoc xs y z) ⟩
      consS x (xs ++-raw (y ++-raw z))
    ∎
    where open import Relation.Binary.Reasoning.Setoid ≈ₛ-setoid

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

  NormalSemigroup : Set a
  NormalSemigroup = Σ[ x ∈ Semigroup ] (Normal x)

  pattern nleaf₁ x = leaf₁ x , Sleaf
  pattern nleaf₂ x = leaf₂ x , Dleaf
  pattern nScons x xs p = cons₁ x xs , Scons p
  pattern nDcons x xs p = cons₂ x xs , Dcons p

  infix 6 _≈ₙ_

  _≈ₙ_ : NormalSemigroup → NormalSemigroup → Set (a ⊔ ℓ)
  (x , _) ≈ₙ (y , _) = x ≈ₛ y

  ≈ₙ-isEquivalence : IsEquivalence _≈ₙ_
  ≈ₙ-isEquivalence = record { refl  = ≈ₛ-refl
                            ; sym   = ≈ₛ-sym
                            ; trans = ≈ₛ-trans
                            }

  ≈ₙ-setoid : Setoid a (a ⊔ ℓ)
  ≈ₙ-setoid = record { Carrier       = NormalSemigroup
                     ; _≈_           = _≈ₙ_
                     ; isEquivalence = ≈ₙ-isEquivalence
                     }

  open module N = Setoid ≈ₙ-setoid hiding (_≈_)

  _++_ : NormalSemigroup → NormalSemigroup → NormalSemigroup
  ( x , p ) ++ ( y , q ) =  x ++-raw y , p ++ₙ q

  ++-assoc : ∀ (x y z : NormalSemigroup)
             → (x ++ y) ++ z ≈ₙ x ++ (y ++ z)
  ++-assoc (x , _) (y , _) (z , _) = ++-raw-assoc x y z

  ++-⟦_⟧ : Interpretation ≈ₙ-setoid
  ++-⟦ • ⟧ (x ∷ y ∷ []) = x ++ y

  ++-⟦⟧-cong : Congruence ≈ₙ-setoid ++-⟦_⟧
  ++-⟦⟧-cong • (x≈ₛy ∷ z≈ₛw ∷ []) = ++-raw-cong x≈ₛy z≈ₛw

  ++-isAlgebra : IsAlgebra ≈ₙ-setoid
  ++-isAlgebra = record { ⟦_⟧     = ++-⟦_⟧
                        ; ⟦⟧-cong = ++-⟦⟧-cong
                        }

  ++-algebra : Algebra
  ++-algebra = algebra ≈ₙ-setoid ++-isAlgebra

  ++-models : Models ++-algebra
  ++-models assoc {θ} = ++-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

  ++-isModel : IsModel ≈ₙ-setoid
  ++-isModel = record { isAlgebra = ++-isAlgebra
                      ; models    = ++-models
                      }

  ++-model : Model
  ++-model = record { ∥_∥/≈   = ≈ₙ-setoid
                    ; isModel = ++-isModel
                    }

  ++-inl : ∥ M ∥ → NormalSemigroup
  ++-inl a = nleaf₁ a

  ++-inl-hom : Homomorphic ∥ M ∥ₐ ++-algebra ++-inl
  ++-inl-hom • (x ∷ y ∷ []) = N.refl {x = _ , Sleaf}

  ++-inlₕ : ∥ M ∥ₐ →ₕ ++-algebra
  ++-inlₕ = record { ∥_∥ₕ      = ++-inl
                   ; ∥_∥ₕ-cong = ≈-leaf ∘ ≈-sta
                   ; ∥_∥ₕ-hom  = ++-inl-hom
                   }

  ++-inr-θ : Fin n → NormalSemigroup
  ++-inr-θ k = nleaf₂ k

  ++-inrₕ : ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ++-algebra
  ++-inrₕ = substₕ ++-model ++-inr-θ

  module _ {b ℓ} {W : Model {b} {ℓ}} where

    open module W = Setoid ∥ W ∥/≈ renaming (_≈_ to _≈W_)

    private
      _⊕_ : ∥ W ∥ → ∥ W ∥ → ∥ W ∥
      x ⊕ y = (W ⟦ • ⟧) (x ∷ y ∷ [])

      ⊕-cong : ∀ {x y z w} → x ≈W y → z ≈W w → x ⊕ z ≈W y ⊕ w
      ⊕-cong x≈Wy z≈Ww = (W ⟦⟧-cong) • (x≈Wy ∷ z≈Ww ∷ [])

      ⊕-assoc : ∀ (x y z : ∥ W ∥) → (x ⊕ y) ⊕ z ≈W x ⊕ (y ⊕ z)
      ⊕-assoc x y z = ∥ W ∥ₐ-models assoc {θ = θ}
        where θ : Fin 3 → ∥ W ∥
              θ zero             = x
              θ (suc zero)       = y
              θ (suc (suc zero)) = z

    module _
      {f : ∥ M ∥ₐ →ₕ ∥ W ∥ₐ}
      {g : ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ∥ W ∥ₐ}
      where

      ++-[_,_]BT : BT n ∥ M ∥ → ∥ W ∥
      ++-[_,_]BT (sta x) = ∥ f ∥ₕ x
      ++-[_,_]BT (dyn x) = ∥ g ∥ₕ (term₂ x)

      ++-[_,_]BT-cong : Congruent _≈BT_ _≈W_ (++-[_,_]BT)
      ++-[_,_]BT-cong (≈-sta x) = ∥ f ∥ₕ-cong x
      ++-[_,_]BT-cong (≡-dyn x) =
        ∥ g ∥ₕ-cong (T.reflexive (PE.cong term₂ x))

      ++-[_,_]-raw : Semigroup → ∥ W ∥
      ++-[_,_]-raw (leaf x)    = ++-[_,_]BT x
      ++-[_,_]-raw (cons x xs) = ++-[_,_]BT x ⊕ ++-[_,_]-raw xs

      ++-[_,_] : NormalSemigroup → ∥ W ∥
      ++-[_,_] (x , _) = ++-[_,_]-raw x

      ++-[_,_]-raw-cong : Congruent _≈ₛ_ _≈W_ ++-[_,_]-raw
      ++-[_,_]-raw-cong (≈-leaf p)   = ++-[_,_]BT-cong p
      ++-[_,_]-raw-cong (≈-cons p q) =
        ⊕-cong (++-[_,_]BT-cong p) (++-[_,_]-raw-cong q)

      open import Relation.Binary.Reasoning.Setoid ∥ W ∥/≈

      ++-[_,_]-hom : ∀ (x y : NormalSemigroup)
                     → (++-[_,_] x ⊕ ++-[_,_] y) ≈W ++-[_,_] (x ++ y)
      ++-[_,_]-hom (nleaf₁ x) (nleaf₁ y)     = ∥ f ∥ₕ-hom • (x ∷ y ∷ [])
      ++-[_,_]-hom (nleaf₁ x) (nleaf₂ _)     = W.refl
      ++-[_,_]-hom (nleaf₁ x) (nScons y z p) = begin
          ∥ f ∥ₕ x ⊕ (∥ f ∥ₕ y ⊕ ++-[_,_]-raw z)
        ≈⟨ W.sym (⊕-assoc (∥ f ∥ₕ x) (∥ f ∥ₕ y) (++-[_,_]-raw z)) ⟩
          (∥ f ∥ₕ x ⊕ ∥ f ∥ₕ y) ⊕ ++-[_,_]-raw z
        ≈⟨ ⊕-cong (∥ f ∥ₕ-hom • (x ∷ y ∷ [])) W.refl ⟩
          ∥ f ∥ₕ (x · y) ⊕ ++-[_,_]-raw z
        ∎
      ++-[_,_]-hom (nleaf₁ x) (nDcons _ _ _) = ⊕-cong W.refl W.refl
      ++-[_,_]-hom (nleaf₂ _) _              = W.refl
      ++-[_,_]-hom (nScons x y p) z          = begin
          (∥ f ∥ₕ x ⊕ ++-[_,_]-raw y) ⊕ ++-[_,_] z
        ≈⟨ ⊕-assoc (∥ f ∥ₕ x) (++-[_,_]-raw y) (++-[_,_] z) ⟩
          ∥ f ∥ₕ x ⊕ (++-[_,_]-raw y ⊕ ++-[_,_] z)
        ≈⟨ ⊕-cong W.refl (++-[_,_]-hom (y , dnorm p) z) ⟩
          ∥ f ∥ₕ x ⊕ ++-[_,_] ((y , dnorm p) ++ z)
        ≈⟨ ++-[_,_]-raw-cong (S.reflexive (consSD-lemma (++-D p (proj₂ z)))) ⟩
          ++-[_,_]-raw (consS x (y ++-raw (proj₁ z)))
        ≈⟨ W.sym (++-[_,_]-raw-cong (consS-++ {a = x} y (proj₁ z))) ⟩
          ++-[_,_]-raw ((consS x y) ++-raw (proj₁ z))
        ≈⟨ W.sym (++-[_,_]-raw-cong (++-raw-cong (S.reflexive (consSD-lemma p)) S.refl)) ⟩
          ++-[_,_]-raw ((cons₁ x y) ++-raw (proj₁ z))
        ∎
      ++-[_,_]-hom (nDcons x xs p) y         = begin
          (∥ g ∥ₕ (term₂ x) ⊕ ++-[_,_] (xs , p)) ⊕ ++-[_,_] y
        ≈⟨ ⊕-assoc (∥ g ∥ₕ (term₂ x)) (++-[_,_]-raw xs) (++-[_,_] y) ⟩
          ∥ g ∥ₕ (term₂ x) ⊕ (++-[_,_] (xs , p) ⊕ ++-[_,_] y)
        ≈⟨ ⊕-cong W.refl (++-[_,_]-hom (xs , p) y) ⟩
          ∥ g ∥ₕ (term₂ x) ⊕ ++-[_,_] ((xs , p) ++ y)
        ∎

      ++-[_,_]ₕ : ++-algebra →ₕ ∥ W ∥ₐ
      ++-[_,_]ₕ = record { ∥_∥ₕ      = ++-[_,_]
                         ; ∥_∥ₕ-cong = ++-[_,_]-raw-cong
                         ; ∥_∥ₕ-hom  = hom
                         }
        where hom : Homomorphic ++-algebra ∥ W ∥ₐ ++-[_,_]
              hom • (x ∷ y ∷ []) = ++-[_,_]-hom x y

      ++-[_,_]-commute₁ : ++-[_,_]ₕ ∘ₕ ++-inlₕ ≡ₕ f
      ++-[_,_]-commute₁ = W.refl

      ++-[_,_]-commute₂ : ++-[_,_]ₕ ∘ₕ ++-inrₕ ≡ₕ g
      ++-[_,_]-commute₂ {x = term₂ k} =
        ++-[_,_]-raw-cong (S.refl {x = proj₁ (++-inr-θ k)})
      ++-[_,_]-commute₂ {x = t@(term • (x ∷ y ∷ []))} = begin
          ++-[_,_] (subst ++-algebra ++-inr-θ t)
        ≈⟨ ++-[_,_]-raw-cong (subst-hom ++-model ++-inr-θ • (x ∷ y ∷ [])) ⟩
          ++-[_,_] (subst-x ++ subst-y)
        ≈⟨ W.sym (++-[_,_]-hom subst-x subst-y) ⟩
          (++-[_,_] subst-x) ⊕ (++-[_,_] subst-y)
        ≈⟨ ⊕-cong ++-[_,_]-commute₂ ++-[_,_]-commute₂ ⟩
          ∥ g ∥ₕ x ⊕ ∥ g ∥ₕ y
        ≈⟨ ∥ g ∥ₕ-hom • (x ∷ y ∷ []) ⟩
          ∥ g ∥ₕ t
        ∎
        where subst-x = subst ++-algebra ++-inr-θ x
              subst-y = subst ++-algebra ++-inr-θ y

      module _ {h : ++-algebra →ₕ ∥ W ∥ₐ} where

        ++-[_,_]-universal : h ∘ₕ ++-inlₕ ≡ₕ f → h ∘ₕ ++-inrₕ ≡ₕ g
                             → ++-[_,_]ₕ ≡ₕ h
        ++-[_,_]-universal c₁ c₂ {nleaf₁ x}     = W.sym c₁
        ++-[_,_]-universal c₁ c₂ {nleaf₂ x}     = W.sym c₂
        ++-[_,_]-universal c₁ c₂ {nScons x y p} = begin
            ∥ f ∥ₕ x ⊕ ++-[_,_] (y , dnorm p)
          ≈⟨ ⊕-cong (W.sym c₁) (++-[_,_]-universal c₁ c₂) ⟩
            ∥ h ∥ₕ (nleaf₁ x) ⊕ ∥ h ∥ₕ (y , dnorm p)
          ≈⟨ ∥ h ∥ₕ-hom • (nleaf₁ x ∷ (y , dnorm p) ∷ []) ⟩
            ∥ h ∥ₕ (consS x y , consS-preserves (dnorm p))
          ≈⟨ W.sym (∥ h ∥ₕ-cong (S.reflexive (consSD-lemma p))) ⟩
            ∥ h ∥ₕ (nScons x y p)
          ∎
        ++-[_,_]-universal c₁ c₂ {nDcons x y p} = begin
            ∥ g ∥ₕ (term₂ x) ⊕ ++-[_,_] (y , p)
          ≈⟨ ⊕-cong (W.sym c₂) (++-[_,_]-universal c₁ c₂) ⟩
            ∥ h ∥ₕ (nleaf₂ x) ⊕ ∥ h ∥ₕ (y , p)
          ≈⟨ ∥ h ∥ₕ-hom • (nleaf₂ x ∷ (y , p) ∷ []) ⟩
            ∥ h ∥ₕ ((nleaf₂ x) ++ (y , p))
          ∎

++-model-isFrex : IsFreeExtension ++-model
++-model-isFrex M n =
  record { inl       = ++-inlₕ M n
         ; inr       = ++-inrₕ M n
         ; [_,_]     = λ f → λ g → ++-[_,_]ₕ M n {f = f} {g = g}
         ; commute₁  = λ {_} {_} {W} {f} {g} → ++-[_,_]-commute₁ M n {W = W} {f = f} {g = g}
         ; commute₂  = λ {_} {_} {W} {f} {g} → ++-[_,_]-commute₂ M n {W = W} {f = f} {g = g}
         ; universal = λ {_} {_} {W} {f} {g} {h} → ++-[_,_]-universal M n {W = W} {f = f} {g = g} {h = h}
         }

SemigroupFrex : FreeExtension
SemigroupFrex = record { _[_]        = ++-model
                       ; _[_]-isFrex = ++-model-isFrex
                       }
