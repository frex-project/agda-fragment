{-# OPTIONS --without-K --safe #-}

open import Fragment.Equational.Bundles
  using (Θ-semigroup; Σ-magma; MagmaOp; SemigroupEq)
open import Fragment.Equational.Model

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

module Fragment.Extensions.Semigroup {a}
  {A : Set a}
  (isModel : IsModel Θ-semigroup (PE.setoid A))
  (n : ℕ)
  where

open import Fragment.Equational.Structures using (isModel→semigroup)
open import Fragment.Equational.FreeExtension Θ-semigroup
open import Fragment.Equational.FreeModel

open import Fragment.Algebra.Algebra
open import Fragment.Algebra.Signature renaming (_⦉_⦊ to _⦉_⦊ₜ)
open import Fragment.Algebra.TermAlgebra (Σ-magma ⦉ n ⦊ₜ)
open import Fragment.Algebra.Homomorphism (Σ-magma)

open import Function.Bundles using (Inverse)
open import Algebra.Structures using (IsSemigroup)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡↔≡)
open import Data.Fin using (Fin; #_)
open import Data.Vec using (Vec; _∷_; []; map)
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡)

open IsModel isModel
open IsSemigroup (isModel→semigroup (PE.setoid A) isModel)

private
  M : Model Θ-semigroup
  M = record { Carrierₛ = (PE.setoid A)
             ; isModel  = isModel
             }

  S : Algebra Σ-magma
  S = algebra (PE.setoid A) isAlgebra

_•_ : A → A → A
x • y = ⟦ MagmaOp.• ⟧ (x ∷ y ∷ [])

data Semigroup : Set a where
  leaf : A ⊎ Fin n → Semigroup
  cons : A ⊎ Fin n → Semigroup → Semigroup

consS : A → Semigroup → Semigroup
consS a (leaf (inj₁ x))    = leaf (inj₁ (a • x))
consS a (cons (inj₁ x) xs) = cons (inj₁ (a • x)) xs
consS a x                  = cons (inj₁ a) x

consD : Fin n → Semigroup → Semigroup
consD a x = cons (inj₂ a) x

normalise : Semigroup → Semigroup
normalise (cons (inj₁ x) xs) = consS x (normalise xs)
normalise (cons (inj₂ x) xs) = consD x (normalise xs)
normalise x                  = x

data Normal : Semigroup → Set a where
  leaf  : ∀ {x} → Normal (leaf x)
  cons₁ : ∀ {x y} → Normal (cons (inj₁ x) (leaf (inj₂ y)))
  cons₂ : ∀ {x xs} → Normal xs → Normal (cons (inj₂ x) xs)
  cons₃ : ∀ {x y ys} → Normal ys → Normal (cons (inj₁ x) (cons (inj₂ y) ys))

canonicity : ∀ {x : Semigroup} → (p : Normal x) → (q : Normal x) → p ≡ q
canonicity {x = leaf _} leaf leaf                                     = PE.refl
canonicity {x = cons (inj₁ x) (leaf (inj₂ _))} cons₁ cons₁            = PE.refl
canonicity {x = cons (inj₁ x) (cons (inj₂ y) ys)} (cons₃ p) (cons₃ q) =
  PE.cong cons₃ (canonicity p q)
canonicity {x = cons (inj₂ x) xs} (cons₂ p) (cons₂ q)                 =
  PE.cong cons₂ (canonicity p q)

consS-preserves : ∀ {x xs} → Normal xs → Normal (consS x xs)
consS-preserves (leaf {x = inj₁ y}) = leaf
consS-preserves (leaf {x = inj₂ y}) = cons₁
consS-preserves cons₁     = cons₁
consS-preserves (cons₂ p) = cons₃ p
consS-preserves (cons₃ p) = cons₃ p

normalise-reduction : ∀ {x} → Normal (normalise x)
normalise-reduction {x = leaf x}           = leaf
normalise-reduction {x = cons (inj₁ x) xs} = consS-preserves (normalise-reduction {x = xs})
normalise-reduction {x = cons (inj₂ x) xs} = cons₂ (normalise-reduction {x = xs})

_++-raw_ : Semigroup → Semigroup → Semigroup
leaf (inj₁ x)    ++-raw y = consS x y
leaf (inj₂ x)    ++-raw y = consD x y
cons (inj₁ x) xs ++-raw y = consS x (xs ++-raw y)
cons (inj₂ x) xs ++-raw y = consD x (xs ++-raw y)

consS-• : ∀ {a b} → (x : Semigroup) → consS (a • b) x ≡ consS a (consS b x)
consS-• {a = a} {b = b} (leaf (inj₁ x))    = PE.cong (λ x → leaf (inj₁ x)) (assoc a b x)
consS-• {a = a} {b = b} (cons (inj₁ x) xs) = PE.cong (λ x → cons (inj₁ x) xs) (assoc a b x)
consS-• (leaf (inj₂ x))                    = PE.refl
consS-• (cons (inj₂ x) xs)                 = PE.refl

consS-++ : ∀ {a} → (x y : Semigroup)
              → (consS a x) ++-raw y ≡ consS a (x ++-raw y)
consS-++ {a = a} (leaf (inj₁ x)) (leaf (inj₁ y))    = PE.cong (λ x → leaf (inj₁ x)) (assoc a x y)
consS-++ {a = a} (leaf (inj₁ x)) (cons (inj₁ y) ys) = PE.cong (λ x → cons (inj₁ x) ys) (assoc a x y)
consS-++ (leaf (inj₁ x)) (leaf (inj₂ y))    = PE.refl
consS-++ (leaf (inj₁ x)) (cons (inj₂ y) ys) = PE.refl
consS-++ (leaf (inj₂ x)) y                  = PE.refl
consS-++ (cons (inj₂ x) xs) y               = PE.refl
consS-++ {a = a} (cons (inj₁ x) xs) y = begin
    (consS a (cons (inj₁ x) xs)) ++-raw y
  ≡⟨ PE.cong (_++-raw y) (PE.refl {x = cons (inj₁ (a • x)) xs}) ⟩
    (cons (inj₁ (a • x)) xs) ++-raw y
  ≡⟨⟩
    consS (a • x) (xs ++-raw y)
  ≡⟨ consS-• (xs ++-raw y) ⟩
    consS a ((cons (inj₁ x) xs) ++-raw y)
  ∎
  where open PE.≡-Reasoning

++-raw-assoc : ∀ (x y z : Semigroup)
               → (x ++-raw y) ++-raw z ≡ x ++-raw (y ++-raw z)
++-raw-assoc (leaf (inj₁ x)) (leaf (inj₁ y)) (leaf (inj₂ z)) = PE.refl
++-raw-assoc (leaf (inj₁ x)) (leaf (inj₂ y)) z               = PE.refl
++-raw-assoc (leaf (inj₂ x)) y z                             = PE.refl
++-raw-assoc (leaf (inj₁ x)) y z                             = consS-++ y z
++-raw-assoc (cons (inj₂ x) xs) y z                          =
  PE.cong (cons (inj₂ x)) (++-raw-assoc xs y z)
++-raw-assoc (cons (inj₁ x) xs) y z                          = begin
    ((cons (inj₁ x) xs) ++-raw y) ++-raw z
  ≡⟨⟩
    (consS x (xs ++-raw y)) ++-raw z
  ≡⟨ consS-++ (xs ++-raw y) z ⟩
    consS x ((xs ++-raw y) ++-raw z)
  ≡⟨ PE.cong (consS x) (++-raw-assoc xs y z) ⟩
    consS x (xs ++-raw (y ++-raw z))
  ≡⟨⟩
    ((cons (inj₁ x) xs) ++-raw (y ++-raw z))
  ∎
  where open PE.≡-Reasoning

_++ₙ_ : ∀ {x y} →  Normal x → Normal y → Normal (x ++-raw y)
_++ₙ_ {x = leaf (inj₁ x)} {y = y} leaf q                = consS-preserves q
_++ₙ_ {x = leaf (inj₂ x)} {y = y} leaf q                = cons₂ q
_++ₙ_ {x = cons (inj₁ x) (leaf (inj₂ _))} cons₁ q       = cons₃ q
_++ₙ_ {x = cons (inj₁ x) (cons (inj₂ _) _)} (cons₃ p) q = cons₃ (p ++ₙ q)
_++ₙ_ {x = cons (inj₂ x) xs} {y = y} (cons₂ p) q        = cons₂ (p ++ₙ q)

NormalSemigroup : Set a
NormalSemigroup = Σ[ x ∈ Semigroup ] (Normal x)

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

++-⟦_⟧ : Interpretation Σ-magma (PE.setoid (NormalSemigroup))
++-⟦_⟧ MagmaOp.• (x ∷ y ∷ []) = _++_ x y

++-⟦⟧-cong : Congruence Σ-magma (PE.setoid NormalSemigroup) (++-⟦_⟧)
++-⟦⟧-cong MagmaOp.• p = PE.cong (++-⟦_⟧ MagmaOp.•) (≋⇒≡ p)

++-isAlgebra : IsAlgebra Σ-magma (PE.setoid NormalSemigroup)
++-isAlgebra = record { ⟦_⟧     = ++-⟦_⟧
                      ; ⟦⟧-cong = ++-⟦⟧-cong
                      }

++-algebra : Algebra Σ-magma
++-algebra = algebra (PE.setoid NormalSemigroup) ++-isAlgebra

++-models : Models Θ-semigroup ++-algebra
++-models SemigroupEq.assoc {θ} = ++-assoc (θ (# 0)) (θ (# 1)) (θ (# 2))

++-isModel : IsModel Θ-semigroup (PE.setoid NormalSemigroup)
++-isModel = record { isAlgebra = ++-isAlgebra
                    ; models    = ++-models
                    }

++-model : Model Θ-semigroup
++-model = record { Carrierₛ = PE.setoid NormalSemigroup
                  ; isModel  = ++-isModel
                  }

++-inl : A → NormalSemigroup
++-inl a = leaf (inj₁ a) , leaf

++-inl-hom : Homomorphic S ++-algebra ++-inl
++-inl-hom MagmaOp.• (x ∷ y ∷ []) = PE.refl

++-inlₕ : S →ₕ ++-algebra
++-inlₕ = record { h      = ++-inl
                 ; h-cong = PE.cong ++-inl
                 ; h-hom  = ++-inl-hom
                 }

module _ {b ℓ} {W : Model Θ-semigroup {b} {ℓ}} where

  open Model W renaming (Carrierₐ to Wₐ; Carrier to U; ⟦_⟧ to W⟦_⟧; ⟦⟧-cong to W⟦⟧-cong)
  open IsSemigroup (isModel→semigroup Carrierₛ (Model.isModel W))
    renaming (assoc to ⊕-assoc)

  private
    _⊕_ : U → U → U
    x ⊕ y = W⟦ MagmaOp.• ⟧ (x ∷ y ∷ [])

    ⊕-cong : ∀ {x y z w : U} → x ≈ y → z ≈ w → x ⊕ z ≈ y ⊕ w
    ⊕-cong p q = W⟦⟧-cong MagmaOp.• (p ∷ q ∷ [])
      where open import Data.Vec.Relation.Binary.Pointwise.Inductive using ([]; _∷_)

  ++-[_,_] : (A → U) → (Expr → U) → NormalSemigroup → U
  ++-[ f , g ] (leaf (inj₁ x) , _)                          = f x
  ++-[ f , g ] (leaf (inj₂ x) , _)                          = g (term (inj₂ x) [])
  ++-[ f , g ] (cons (inj₁ x) (leaf (inj₂ y)) , cons₁)      = f x ⊕ g (term (inj₂ y) [])
  ++-[ f , g ] (cons (inj₁ x) (cons (inj₂ y) ys) , cons₃ p) =
    f x ⊕ ++-[ f , g ] (cons (inj₂ y) ys , cons₂ p)
  ++-[ f , g ] (cons (inj₂ x) xs , cons₂ p)                 =
    g (term (inj₂ x) []) ⊕ ++-[ f , g ] (xs , p)

  ++-[_,_]-cong : (f : A → U) → (g : Expr → U) → Congruent _≡_ _≈_ (++-[ f , g ])
  ++-[ f , g ]-cong p = Model.reflexive W (PE.cong ++-[ f , g ] p)

  open import Relation.Binary.Reasoning.Setoid Carrierₛ

  ++-[_,_]-hom : ∀ {f : A → U} {g : Expr → U}
                 → Homomorphic S Wₐ f
                 → Homomorphic |T| Θ-semigroup ⦉ n ⦊/≈ₘ  Wₐ g
                 → Homomorphic ++-algebra Wₐ ++-[ f , g ]
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf (inj₁ x) , leaf) ∷ (leaf (inj₁ y) , leaf) ∷ []) = f-hom MagmaOp.• (x ∷ y ∷ [])
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf (inj₁ x) , leaf) ∷ (leaf (inj₂ y) , leaf) ∷ []) = Model.refl W
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf (inj₁ x) , leaf) ∷ (cons (inj₁ y) (leaf (inj₂ z)) , cons₁) ∷ []) = begin
      f x ⊕ (f y ⊕ g (term (inj₂ z) []))
    ≈⟨ Model.sym W (⊕-assoc (f x) (f y) (g (term (inj₂ z) []))) ⟩
      (f x ⊕ f y) ⊕ g (term (inj₂ z) [])
    ≈⟨ ⊕-cong (f-hom MagmaOp.• (x ∷ y ∷ [])) (Model.refl W) ⟩
      f (x • y) ⊕ g (term (inj₂ z) [])
    ≡⟨⟩
      ++-[ f , g ] (cons (inj₁ (x • y)) (leaf (inj₂ z)) , cons₁)
    ≡⟨⟩
      ++-[ f , g ] ((leaf (inj₁ (x • y)) , leaf) ++ (leaf (inj₂ z) , leaf))
    ∎
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf (inj₁ x) , leaf) ∷ (cons (inj₁ y) ys , cons₃ p) ∷ []) = {!!}
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf (inj₁ x) , leaf) ∷ (cons (inj₂ y) ys , cons₂ p) ∷ []) = {!!}
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf (inj₂ x) , leaf) ∷ (y , p) ∷ [])                      = Model.refl W
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((cons (inj₁ x) (leaf (inj₂ y)) , cons₁) ∷ (z , q) ∷ [])     = begin
      (f x ⊕ g (term (inj₂ y) [])) ⊕ ++-[ f , g ] (z , q)
    ≈⟨ ⊕-assoc (f x) (g (term (inj₂ y) [])) (++-[ f , g ] (z , q)) ⟩
      f x ⊕ (g (term (inj₂ y) []) ⊕ ++-[ f , g ] (z , q))
    ≡⟨⟩
      f x ⊕ ++-[ f , g ] (cons (inj₂ y) z , cons₂ q)
    ≡⟨⟩
      ++-[ f , g ] (cons (inj₁ x) (cons (inj₂ y) z) , cons₃ q)
    ≡⟨⟩
      ++-[ f , g ] ((cons (inj₁ x) (leaf (inj₂ y)) , cons₁) ++ (z , q))
    ∎
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((cons (inj₁ x) (cons (inj₂ y) z) , cons₃ p) ∷ (w , q) ∷ []) = begin
      (f x ⊕ (g (term (inj₂ y) []) ⊕ ++-[ f , g ] (z , p))) ⊕ ++-[ f , g ] (w , q)
    ≈⟨ ⊕-assoc (f x) (g (term (inj₂ y) []) ⊕ ++-[ f , g ] (z , p)) (++-[ f , g ] (w , q)) ⟩
      f x ⊕ ((g (term (inj₂ y) []) ⊕ ++-[ f , g ] (z , p)) ⊕ ++-[ f , g ] (w , q))
    ≈⟨ ⊕-cong (Model.refl W) (⊕-assoc (g (term (inj₂ y) [])) (++-[ f , g ] (z , p)) (++-[ f , g ] (w , q))) ⟩
      f x ⊕ (g (term (inj₂ y) []) ⊕ (++-[ f , g ] (z , p) ⊕ ++-[ f , g ] (w , q)))
    ≈⟨ Model.sym W (⊕-assoc (f x) (g (term (inj₂ y) [])) ((++-[ f , g ] (z , p) ⊕ ++-[ f , g ] (w , q)))) ⟩
      (f x ⊕ g (term (inj₂ y) [])) ⊕ (++-[ f , g ] (z , p) ⊕ ++-[ f , g ] (w , q))
    ≈⟨ ⊕-cong (Model.refl W) (++-[ f-hom , g-hom ]-hom MagmaOp.• ((z , p) ∷ (w , q) ∷ [])) ⟩
      (f x ⊕ g (term (inj₂ y) [])) ⊕ ++-[ f , g ] ((z , p) ++ (w , q))
    ≈⟨ ⊕-assoc (f x) (g (term (inj₂ y) [])) (++-[ f , g ] ((z ++-raw w) , (p ++ₙ q))) ⟩
      f x ⊕ (g (term (inj₂ y) []) ⊕ ++-[ f , g ] ((z , p) ++ (w , q)))
    ≡⟨⟩
      f x ⊕ ++-[ f , g ] (cons (inj₂ y) (z ++-raw w) , cons₂ (p ++ₙ q))
    ≡⟨⟩
      ++-[ f , g ] (cons (inj₁ x) (cons (inj₂ y) (z ++-raw w)) , cons₃ (p ++ₙ q))
    ≡⟨⟩
      ++-[ f , g ] ((cons (inj₁ x) (cons (inj₂ y) z) , cons₃ p) ++ (w , q))
    ∎
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((cons (inj₂ x) xs , cons₂ p) ∷ (y , q) ∷ [])                = begin
      (g (term (inj₂ x) []) ⊕ ++-[ f ,  g ] (xs , p)) ⊕ ++-[ f , g ] (y , q)
    ≈⟨ ⊕-assoc (g (term (inj₂ x) [])) (++-[ f , g ] (xs , p)) (++-[ f , g ] (y , q)) ⟩
      g (term (inj₂ x) []) ⊕ (++-[ f ,  g ] (xs , p) ⊕ ++-[ f , g ] (y , q))
    ≈⟨ ⊕-cong (Model.refl W) (++-[ f-hom , g-hom ]-hom MagmaOp.• ((xs , p) ∷ (y , q) ∷ [])) ⟩
      g (term (inj₂ x) []) ⊕ ++-[ f , g ] (xs ++-raw y , p ++ₙ q)
    ≡⟨⟩
      ++-[ f , g ] ((cons (inj₂ x) (xs ++-raw y)) , cons₂ (p ++ₙ q))
    ≡⟨⟩
      ++-[ f , g ] ((cons (inj₂ x) xs , cons₂ p) ++ (y , q))
    ∎

  ++-[_,_]ₕ : S →ₕ Wₐ → |T| Θ-semigroup ⦉ n ⦊/≈ₘ →ₕ Wₐ → ++-algebra →ₕ Wₐ
  ++-[_,_]ₕ F G = record { h      = ++-[ _→ₕ_.h F , _→ₕ_.h G ]
                         ; h-cong = ++-[ _→ₕ_.h F , _→ₕ_.h G ]-cong
                         ; h-hom  = ++-[ _→ₕ_.h-hom F , _→ₕ_.h-hom G ]-hom
                         }

++-isFrex : IsFreeExtension M n ++-model
++-isFrex = record { inl       = ++-inlₕ
                   ; inr       = substₕ ++-model (λ k → leaf (inj₂ k) , leaf)
                   ; [_,_]     = λ {_} {_} {W} → ++-[_,_]ₕ {W = W}
                   ; commute₁  = {!!}
                   ; commute₂  = {!!}
                   ; universal = {!!}
                   }
