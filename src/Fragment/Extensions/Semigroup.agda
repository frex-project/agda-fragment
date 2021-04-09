{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Bundles
  using (Θ-semigroup; Σ-magma; MagmaOp; SemigroupEq)
open import Fragment.Equational.Model Θ-semigroup

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

module Fragment.Extensions.Semigroup {a}
  {A : Set a}
  (isModel : IsModel (PE.setoid A))
  (n : ℕ)
  where

open import Fragment.Equational.Structures using (isModel→semigroup)
open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.FreeModel Θ-semigroup

open import Fragment.Algebra.Signature
open import Fragment.Algebra.TermAlgebra (Σ-magma ⦉ n ⦊)
open import Fragment.Algebra.Homomorphism Σ-magma
open import Fragment.Algebra.Homomorphism.Setoid Σ-magma
open import Fragment.Algebra.FreeAlgebra Σ-magma using (subst; term₁; term₂)
open import Fragment.Algebra.Algebra Σ-magma
  using (Algebra; IsAlgebra; Interpretation; Congruence; algebra)

open import Function.Bundles using (Inverse)
open import Algebra.Structures using (IsSemigroup)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡↔≡)
open import Data.Fin using (Fin; #_)
open import Data.Vec using (Vec; _∷_; []; map)
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)

open import Relation.Binary using (Setoid)

open IsSemigroup (isModel→semigroup (PE.setoid A) isModel) using (assoc)

private
  M : Model
  M = model (PE.setoid A) isModel

  _•_ : A → A → A
  x • y = (Model._⟦_⟧ M MagmaOp.•) (x ∷ y ∷ [])

data Semigroup : Set a where
  leaf : A ⊎ Fin n → Semigroup
  cons : A ⊎ Fin n → Semigroup → Semigroup

pattern leaf₁ x = leaf (inj₁ x)
pattern leaf₂ x = leaf (inj₂ x)
pattern cons₁ x xs = cons (inj₁ x) xs
pattern cons₂ x ys = cons (inj₂ x) ys

consS : A → Semigroup → Semigroup
consS a (leaf₁ x)    = leaf₁ (a • x)
consS a (cons₁ x xs) = cons₁ (a • x) xs
consS a x            = cons₁ a x

consD : Fin n → Semigroup → Semigroup
consD a x = cons₂ a x

normalise : Semigroup → Semigroup
normalise (cons₁ x xs) = consS x (normalise xs)
normalise (cons₂ x xs) = consD x (normalise xs)
normalise x            = x

data Normal : Semigroup → Set a where
  isleaf : ∀ {x} → Normal (leaf x)
  SDleaf : ∀ {x y} → Normal (cons₁ x (leaf₂ y))
  Dcons  : ∀ {x xs} → Normal xs → Normal (cons₂ x xs)
  SDcons : ∀ {x y ys} → Normal ys → Normal (cons₁ x (cons₂ y ys))

canonicity : ∀ {x : Semigroup} → (p : Normal x) → (q : Normal x) → p ≡ q
canonicity {x = leaf _} isleaf isleaf                       = PE.refl
canonicity {x = cons₁ x (leaf₂ _)} SDleaf SDleaf            = PE.refl
canonicity {x = cons₁ x (cons₂ y ys)} (SDcons p) (SDcons q) =
  PE.cong SDcons (canonicity p q)
canonicity {x = cons₂ x xs} (Dcons p) (Dcons q)             =
  PE.cong Dcons (canonicity p q)

consS-preserves : ∀ {x xs} → Normal xs → Normal (consS x xs)
consS-preserves (isleaf {x = inj₁ y}) = isleaf
consS-preserves (isleaf {x = inj₂ y}) = SDleaf
consS-preserves SDleaf                = SDleaf
consS-preserves (Dcons p)             = SDcons p
consS-preserves (SDcons p)            = SDcons p

normalise-reduction : ∀ {x} → Normal (normalise x)
normalise-reduction {x = leaf x}     = isleaf
normalise-reduction {x = cons₁ x xs} = consS-preserves (normalise-reduction {x = xs})
normalise-reduction {x = cons₂ x xs} = Dcons (normalise-reduction {x = xs})

_++-raw_ : Semigroup → Semigroup → Semigroup
leaf₁ x    ++-raw y = consS x y
leaf₂ x    ++-raw y = consD x y
cons₁ x xs ++-raw y = consS x (xs ++-raw y)
cons₂ x xs ++-raw y = consD x (xs ++-raw y)

consS-• : ∀ {a b} → (x : Semigroup) → consS (a • b) x ≡ consS a (consS b x)
consS-• {a = a} {b = b} (leaf₁ x)    = PE.cong (λ x → leaf₁ x) (assoc a b x)
consS-• {a = a} {b = b} (cons₁ x xs) = PE.cong (λ x → cons₁ x xs) (assoc a b x)
consS-• (leaf₂ x)                    = PE.refl
consS-• (cons₂ x xs)                 = PE.refl

consS-++ : ∀ {a} → (x y : Semigroup)
           → (consS a x) ++-raw y ≡ consS a (x ++-raw y)
consS-++ {a = a} (leaf₁ x) (leaf₁ y)    = PE.cong (λ x → leaf₁ x) (assoc a x y)
consS-++ {a = a} (leaf₁ x) (cons₁ y ys) = PE.cong (λ x → cons₁ x ys) (assoc a x y)
consS-++ (leaf₁ x) (leaf₂ y)            = PE.refl
consS-++ (leaf₁ x) (cons₂ y ys)         = PE.refl
consS-++ (leaf₂ x) y                    = PE.refl
consS-++ (cons₂ x xs) y                 = PE.refl
consS-++ {a = a} (cons₁ x xs) y = begin
    (consS a (cons₁ x xs)) ++-raw y
  ≡⟨ PE.cong (_++-raw y) (PE.refl {x = cons₁ (a • x) xs}) ⟩
    (cons₁ (a • x) xs) ++-raw y
  ≡⟨⟩
    consS (a • x) (xs ++-raw y)
  ≡⟨ consS-• (xs ++-raw y) ⟩
    consS a ((cons₁ x xs) ++-raw y)
  ∎
  where open PE.≡-Reasoning

++-raw-assoc : ∀ (x y z : Semigroup)
               → (x ++-raw y) ++-raw z ≡ x ++-raw (y ++-raw z)
++-raw-assoc (leaf₁ x) (leaf₁ y) (leaf₂ z) = PE.refl
++-raw-assoc (leaf₁ x) (leaf₂ y) z         = PE.refl
++-raw-assoc (leaf₂ x) y z                 = PE.refl
++-raw-assoc (leaf₁ x) y z                 = consS-++ y z
++-raw-assoc (cons₂ x xs) y z              =
  PE.cong (cons₂ x) (++-raw-assoc xs y z)
++-raw-assoc (cons₁ x xs) y z              = begin
    (consS x (xs ++-raw y)) ++-raw z
  ≡⟨ consS-++ (xs ++-raw y) z ⟩
    consS x ((xs ++-raw y) ++-raw z)
  ≡⟨ PE.cong (consS x) (++-raw-assoc xs y z) ⟩
    consS x (xs ++-raw (y ++-raw z))
  ∎
  where open PE.≡-Reasoning

_++ₙ_ : ∀ {x y} →  Normal x → Normal y → Normal (x ++-raw y)
_++ₙ_ {x = leaf₁ x} {y = y} isleaf q         = consS-preserves q
_++ₙ_ {x = leaf₂ x} {y = y} isleaf q         = Dcons q
_++ₙ_ {x = cons₁ x (leaf₂ _)} SDleaf q       = SDcons q
_++ₙ_ {x = cons₁ x (cons₂ _ _)} (SDcons p) q = SDcons (p ++ₙ q)
_++ₙ_ {x = cons₂ x xs} {y = y} (Dcons p) q   = Dcons (p ++ₙ q)

NormalSemigroup : Set a
NormalSemigroup = Σ[ x ∈ Semigroup ] (Normal x)

pattern nleaf₁ x    = leaf₁ x , isleaf
pattern nleaf₂ x    = leaf₂ x , isleaf
pattern nSDleaf x y      = cons₁ x (leaf₂ y) , SDleaf
pattern nDcons x xs p    = cons₂ x xs , Dcons p
pattern nSDcons x y ys p = cons₁ x (cons₂ y ys) , SDcons p

_++_ : NormalSemigroup → NormalSemigroup → NormalSemigroup
( x , p ) ++ ( y , q ) =  x ++-raw y , p ++ₙ q

++-assoc : ∀ (x y z : NormalSemigroup)
           → (x ++ y) ++ z ≡ x ++ (y ++ z)
++-assoc (x , p) (y , q) (z , r) =
  Inverse.f Σ-≡,≡↔≡
    (++-raw-assoc x y z ,
      canonicity
        (PE.subst Normal (++-raw-assoc x y z) ((p ++ₙ q) ++ₙ r))
        (p ++ₙ (q ++ₙ r)))

++-⟦_⟧ : Interpretation (PE.setoid (NormalSemigroup))
++-⟦_⟧ MagmaOp.• (x ∷ y ∷ []) = _++_ x y

++-⟦⟧-cong : Congruence (PE.setoid NormalSemigroup) (++-⟦_⟧)
++-⟦⟧-cong MagmaOp.• p = PE.cong (++-⟦_⟧ MagmaOp.•) (≋⇒≡ p)

++-isAlgebra : IsAlgebra (PE.setoid NormalSemigroup)
++-isAlgebra = record { ⟦_⟧     = ++-⟦_⟧
                      ; ⟦⟧-cong = ++-⟦⟧-cong
                      }

++-algebra : Algebra
++-algebra = algebra (PE.setoid NormalSemigroup) ++-isAlgebra

++-models : Models ++-algebra
++-models SemigroupEq.assoc {θ} = ++-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

++-isModel : IsModel (PE.setoid NormalSemigroup)
++-isModel = record { isAlgebra = ++-isAlgebra
                    ; models    = ++-models
                    }

++-model : Model
++-model = record { ∥_∥/≈   = PE.setoid NormalSemigroup
                  ; isModel = ++-isModel
                  }

++-inl : A → NormalSemigroup
++-inl a = leaf₁ a , isleaf

++-inl-hom : Homomorphic ∥ M ∥ₐ ++-algebra ++-inl
++-inl-hom MagmaOp.• (x ∷ y ∷ []) = PE.refl

++-inlₕ : ∥ M ∥ₐ →ₕ ++-algebra
++-inlₕ = record { ∥_∥ₕ      = ++-inl
                 ; ∥_∥ₕ-cong = PE.cong ++-inl
                 ; ∥_∥ₕ-hom  = ++-inl-hom
                 }

++-inr-θ : Fin n → NormalSemigroup
++-inr-θ k = leaf₂ k , isleaf

++-inrₕ : ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ++-algebra
++-inrₕ = substₕ ++-model ++-inr-θ

module _ {b ℓ} {W : Model {b} {ℓ}} where

  open Setoid ∥ W ∥/≈

  open IsSemigroup (isModel→semigroup ∥ W ∥/≈ (Model.isModel W))
    using ()
    renaming (assoc to ⊕-assoc)

  private
    _⊕_ : ∥ W ∥ → ∥ W ∥ → ∥ W ∥
    x ⊕ y = (W ⟦ MagmaOp.• ⟧) (x ∷ y ∷ [])

    ⊕-cong : ∀ {x y z w : ∥ W ∥} → x ≈ y → z ≈ w → x ⊕ z ≈ y ⊕ w
    ⊕-cong p q = (W ⟦⟧-cong) MagmaOp.• (p ∷ q ∷ [])
      where open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

  ++-[_,_] : (A → ∥ W ∥) → (Expr → ∥ W ∥) → NormalSemigroup → ∥ W ∥
  ++-[ f , g ] (nleaf₁ x)         = f x
  ++-[ f , g ] (nleaf₂ x)         = g (term₂ x)
  ++-[ f , g ] (nSDleaf x y)      = f x ⊕ g (term₂ y)
  ++-[ f , g ] (nSDcons x y ys p) = f x ⊕ ++-[ f , g ] (nDcons y ys p)
  ++-[ f , g ] (nDcons x xs p)    = g (term₂ x) ⊕ ++-[ f , g ] (xs , p)

  ++-[_,_]-cong : (f : A → ∥ W ∥) → (g : Expr → ∥ W ∥) → Congruent _≡_ _≈_ (++-[ f , g ])
  ++-[ f , g ]-cong p = reflexive (PE.cong ++-[ f , g ] p)

  open import Relation.Binary.Reasoning.Setoid ∥ W ∥/≈

  module _ {f : A → ∥ W ∥}
    {g : Expr → ∥ W ∥}
    (f-hom : Homomorphic ∥ M ∥ₐ ∥ W ∥ₐ f)
    (g-hom : Homomorphic ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ  ∥ W ∥ₐ g)
    where

    private
      ++-[] : _
      ++-[] = ++-[ f , g ]

    ++-[_,_]-hom : Homomorphic ++-algebra ∥ W ∥ₐ ++-[ f , g ]
    ++-[_,_]-hom MagmaOp.• (nleaf₁ x ∷ nleaf₁ y ∷ [])     = f-hom MagmaOp.• (x ∷ y ∷ [])
    ++-[_,_]-hom MagmaOp.• (nleaf₁ _ ∷ nleaf₂ _ ∷ [])     = refl
    ++-[_,_]-hom MagmaOp.• (nleaf₁ _ ∷ nDcons _ _ _ ∷ []) = ⊕-cong refl refl
    ++-[_,_]-hom MagmaOp.• (nleaf₂ _ ∷ _ ∷ [])            = refl
    ++-[_,_]-hom MagmaOp.• (nSDleaf x y ∷ z ∷ [])         =
      ⊕-assoc (f x) (g (term₂ y)) (++-[] z)
    ++-[_,_]-hom MagmaOp.• (nleaf₁ x ∷ nSDleaf y z ∷ [])      = begin
        f x ⊕ (f y ⊕ g (term₂ z))
      ≈⟨ sym (⊕-assoc (f x) (f y) (g (term₂ z))) ⟩
        (f x ⊕ f y) ⊕ g (term₂ z)
      ≈⟨ ⊕-cong (f-hom MagmaOp.• (x ∷ y ∷ [])) refl ⟩
        f (x • y) ⊕ g (term₂ z)
      ∎
    ++-[_,_]-hom MagmaOp.• (nleaf₁ x ∷ nSDcons y z w p ∷ [])  = begin
        f x ⊕ (f y ⊕ (g (term₂ z) ⊕ ++-[] (w , p)))
      ≈⟨ sym (⊕-assoc (f x) (f y) (g (term₂ z) ⊕ ++-[] (w , p))) ⟩
        (f x ⊕ f y) ⊕ (g (term₂ z) ⊕ ++-[] (w , p))
      ≈⟨ ⊕-cong (f-hom MagmaOp.• (x ∷ y ∷ [])) refl ⟩
        f (x • y) ⊕ ++-[] ((nleaf₂ z) ++ (w , p))
      ∎
    ++-[_,_]-hom MagmaOp.• (nSDcons x y z p ∷ t@(w , q) ∷ []) = begin
        (f x ⊕ (g (term₂ y) ⊕ ++-[] (z , p))) ⊕ ++-[] t
      ≈⟨ ⊕-assoc (f x) (g (term₂ y) ⊕ ++-[] (z , p)) (++-[] t) ⟩
        f x ⊕ ((g (term₂ y) ⊕ ++-[] (z , p)) ⊕ ++-[] t)
      ≈⟨ ⊕-cong refl (⊕-assoc (g (term₂ y)) (++-[] (z , p)) (++-[] t)) ⟩
        f x ⊕ (g (term₂ y) ⊕ (++-[] (z , p) ⊕ ++-[] t))
      ≈⟨ sym (⊕-assoc (f x) (g (term₂ y)) (++-[] (z , p) ⊕ ++-[] t)) ⟩
        (f x ⊕ g (term₂ y)) ⊕ (++-[] (z , p) ⊕ ++-[] t)
      ≈⟨ ⊕-cong refl (++-[_,_]-hom MagmaOp.• ((z , p) ∷ t ∷ [])) ⟩
        (f x ⊕ g (term₂ y)) ⊕ ++-[] ((z , p) ++ t)
      ≈⟨ ⊕-assoc (f x) (g (term₂ y)) (++-[] (z ++-raw w , p ++ₙ q)) ⟩
        f x ⊕ (g (term₂ y) ⊕ ++-[] ((z , p) ++ t))
      ∎
    ++-[_,_]-hom MagmaOp.• (nDcons x xs p ∷ t@(y , q) ∷ [])   = begin
        (g (term₂ x) ⊕ ++-[] (xs , p)) ⊕ ++-[] t
      ≈⟨ ⊕-assoc (g (term₂ x)) (++-[] (xs , p)) (++-[] t) ⟩
        g (term₂ x) ⊕ (++-[] (xs , p) ⊕ ++-[] t)
      ≈⟨ ⊕-cong refl (++-[_,_]-hom MagmaOp.• ((xs , p) ∷ t ∷ [])) ⟩
        g (term₂ x) ⊕ ++-[] (xs ++-raw y , p ++ₙ q)
      ∎

  ++-[_,_]ₕ : ∥ M ∥ₐ →ₕ ∥ W ∥ₐ → ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ∥ W ∥ₐ → ++-algebra →ₕ ∥ W ∥ₐ
  ++-[_,_]ₕ f g = record { ∥_∥ₕ      = ++-[ ∥ f ∥ₕ , ∥ g ∥ₕ ]
                         ; ∥_∥ₕ-cong = ++-[ ∥ f ∥ₕ , ∥ g ∥ₕ ]-cong
                         ; ∥_∥ₕ-hom  = ++-[ ∥ f ∥ₕ-hom , ∥ g ∥ₕ-hom ]-hom
                         }

  module _ {f : ∥ M ∥ₐ →ₕ ∥ W ∥ₐ} {g : ∥ |T|⦉ n ⦊/≈ₘ ∥ₐ →ₕ ∥ W ∥ₐ} where

    private
      ++-[] : _
      ++-[] = ++-[ ∥ f ∥ₕ , ∥ g ∥ₕ ]

      ++-[]-cong : _
      ++-[]-cong = ++-[ ∥ f ∥ₕ , ∥ g ∥ₕ ]-cong

      ++-[]-hom : _
      ++-[]-hom = ++-[ ∥ f ∥ₕ-hom , ∥ g ∥ₕ-hom ]-hom

    ++-[_,_]-commute₁ : ++-[ f , g ]ₕ ∘ₕ ++-inlₕ ≡ₕ f
    ++-[_,_]-commute₁ = refl

    ++-[_,_]-commute₂ : ++-[ f , g ]ₕ ∘ₕ ++-inrₕ ≡ₕ g
    ++-[_,_]-commute₂ {x = term₂ k} =
      ++-[]-cong (PE.refl {x = ++-inr-θ k})
    ++-[_,_]-commute₂ {x = t@(term (MagmaOp.•) (x ∷ y ∷ []))} = begin
        ++-[] (subst ++-algebra ++-inr-θ t)
      ≈⟨ ++-[]-cong (subst-hom ++-model ++-inr-θ MagmaOp.• (x ∷ y ∷ [])) ⟩
        ++-[] (subst-x ++ subst-y)
      ≈⟨ sym (++-[]-hom MagmaOp.• ( subst-x ∷ subst-y ∷ [])) ⟩
        (++-[] subst-x) ⊕ (++-[] subst-y)
      ≈⟨ ⊕-cong ++-[_,_]-commute₂ ++-[_,_]-commute₂ ⟩
        ∥ g ∥ₕ x ⊕ ∥ g ∥ₕ y
      ≈⟨ ∥ g ∥ₕ-hom MagmaOp.• (x ∷ y ∷ []) ⟩
        ∥ g ∥ₕ t
      ∎
      where subst-x = subst ++-algebra ++-inr-θ x
            subst-y = subst ++-algebra ++-inr-θ y

    module _ {h : ++-algebra →ₕ ∥ W ∥ₐ} where

      ++-[_,_]-universal : h ∘ₕ ++-inlₕ ≡ₕ f → h ∘ₕ ++-inrₕ ≡ₕ g
                           → ++-[ f , g ]ₕ ≡ₕ h
      ++-[ c₁ , c₂ ]-universal {nleaf₁ x} = sym c₁
      ++-[ c₁ , c₂ ]-universal {nleaf₂ x} = sym c₂
      ++-[_,_]-universal c₁ c₂ {nSDleaf x y}         = begin
          ∥ f ∥ₕ x ⊕ ∥ g ∥ₕ (term₂ y)
        ≈⟨ ⊕-cong (sym c₁) (sym c₂) ⟩
          ∥ h ∥ₕ (nleaf₁ x) ⊕ ∥ h ∥ₕ (nleaf₂ y)
        ≈⟨ ∥ h ∥ₕ-hom MagmaOp.• (nleaf₁ x ∷ nleaf₂ y ∷ []) ⟩
          ∥ h ∥ₕ ((nleaf₁ x) ++ (nleaf₂ y))
        ∎
      ++-[_,_]-universal c₁ c₂ {nSDcons x y z p}     = begin
          ∥ f ∥ₕ x ⊕ (∥ g ∥ₕ (term₂ y) ⊕ ++-[] (z , p))
        ≈⟨ ⊕-cong (sym c₁) (⊕-cong (sym c₂) (++-[_,_]-universal c₁ c₂)) ⟩
          ∥ h ∥ₕ (nleaf₁ x) ⊕ (∥ h ∥ₕ (nleaf₂ y) ⊕ ∥ h ∥ₕ (z , p))
        ≈⟨ ⊕-cong refl (∥ h ∥ₕ-hom MagmaOp.• (nleaf₂ y ∷ (z , p) ∷ [])) ⟩
          ∥ h ∥ₕ (nleaf₁ x) ⊕ ∥ h ∥ₕ (nDcons y z p)
        ≈⟨ ∥ h ∥ₕ-hom MagmaOp.• (nleaf₁ x ∷ nDcons y z p ∷ []) ⟩
          ∥ h ∥ₕ (nSDcons x y z p)
        ∎
      ++-[_,_]-universal c₁ c₂ {nDcons x y p} = begin
          ∥ g ∥ₕ (term₂ x) ⊕ ++-[] (y , p)
        ≈⟨ ⊕-cong (sym c₂) (++-[_,_]-universal c₁ c₂) ⟩
          ∥ h ∥ₕ (nleaf₂ x) ⊕ ∥ h ∥ₕ (y , p)
        ≈⟨ ∥ h ∥ₕ-hom MagmaOp.• (nleaf₂ x ∷ (y , p) ∷ []) ⟩
          ∥ h ∥ₕ ((nleaf₂ x) ++ (y , p))
        ∎

++-isFrex : IsFreeExtension M n ++-model
++-isFrex =
  record { inl       = ++-inlₕ
         ; inr       = ++-inrₕ
         ; [_,_]     = λ {_} {_} {W} → ++-[_,_]ₕ {W = W}
         ; commute₁  = λ {_} {_} {W} {f} {g} → ++-[_,_]-commute₁ {W = W} {f = f} {g = g}
         ; commute₂  = λ {_} {_} {W} {f} {g} → ++-[_,_]-commute₂ {W = W} {f = f} {g = g}
         ; universal = λ {_} {_} {W} {f} {g} {h} → ++-[_,_]-universal {W = W} {f = f} {g = g} {h = h}
         }
