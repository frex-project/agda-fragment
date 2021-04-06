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
open import Fragment.Algebra.Homomorphism.Setoid (Σ-magma)
open import Fragment.Algebra.FreeAlgebra using (subst; term₁; term₂)

open import Function.Bundles using (Inverse)
open import Algebra.Structures using (IsSemigroup)

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
  isLeaf : ∀ {x} → Normal (leaf x)
  SDLeaf : ∀ {x y} → Normal (cons₁ x (leaf₂ y))
  DCons  : ∀ {x xs} → Normal xs → Normal (cons₂ x xs)
  SDCons : ∀ {x y ys} → Normal ys → Normal (cons₁ x (cons₂ y ys))

canonicity : ∀ {x : Semigroup} → (p : Normal x) → (q : Normal x) → p ≡ q
canonicity {x = leaf _} isLeaf isLeaf                       = PE.refl
canonicity {x = cons₁ x (leaf₂ _)} SDLeaf SDLeaf            = PE.refl
canonicity {x = cons₁ x (cons₂ y ys)} (SDCons p) (SDCons q) =
  PE.cong SDCons (canonicity p q)
canonicity {x = cons₂ x xs} (DCons p) (DCons q)             =
  PE.cong DCons (canonicity p q)

consS-preserves : ∀ {x xs} → Normal xs → Normal (consS x xs)
consS-preserves (isLeaf {x = inj₁ y}) = isLeaf
consS-preserves (isLeaf {x = inj₂ y}) = SDLeaf
consS-preserves SDLeaf                = SDLeaf
consS-preserves (DCons p)             = SDCons p
consS-preserves (SDCons p)            = SDCons p

normalise-reduction : ∀ {x} → Normal (normalise x)
normalise-reduction {x = leaf x}     = isLeaf
normalise-reduction {x = cons₁ x xs} = consS-preserves (normalise-reduction {x = xs})
normalise-reduction {x = cons₂ x xs} = DCons (normalise-reduction {x = xs})

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
    ((cons₁ x xs) ++-raw y) ++-raw z
  ≡⟨⟩
    (consS x (xs ++-raw y)) ++-raw z
  ≡⟨ consS-++ (xs ++-raw y) z ⟩
    consS x ((xs ++-raw y) ++-raw z)
  ≡⟨ PE.cong (consS x) (++-raw-assoc xs y z) ⟩
    consS x (xs ++-raw (y ++-raw z))
  ≡⟨⟩
    ((cons₁ x xs) ++-raw (y ++-raw z))
  ∎
  where open PE.≡-Reasoning

_++ₙ_ : ∀ {x y} →  Normal x → Normal y → Normal (x ++-raw y)
_++ₙ_ {x = leaf₁ x} {y = y} isLeaf q         = consS-preserves q
_++ₙ_ {x = leaf₂ x} {y = y} isLeaf q         = DCons q
_++ₙ_ {x = cons₁ x (leaf₂ _)} SDLeaf q       = SDCons q
_++ₙ_ {x = cons₁ x (cons₂ _ _)} (SDCons p) q = SDCons (p ++ₙ q)
_++ₙ_ {x = cons₂ x xs} {y = y} (DCons p) q   = DCons (p ++ₙ q)

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
++-inl a = leaf₁ a , isLeaf

++-inl-hom : Homomorphic S ++-algebra ++-inl
++-inl-hom MagmaOp.• (x ∷ y ∷ []) = PE.refl

++-inlₕ : S →ₕ ++-algebra
++-inlₕ = record { h      = ++-inl
                 ; h-cong = PE.cong ++-inl
                 ; h-hom  = ++-inl-hom
                 }

++-inr-θ : Fin n → NormalSemigroup
++-inr-θ k = leaf₂ k , isLeaf

++-inrₕ : |T| Θ-semigroup ⦉ n ⦊/≈ₘ →ₕ ++-algebra
++-inrₕ = substₕ ++-model ++-inr-θ

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
  ++-[ f , g ] (leaf₁ x , _)                     = f x
  ++-[ f , g ] (leaf₂ x , _)                     = g (term₂ x)
  ++-[ f , g ] (cons₁ x (leaf₂ y) , SDLeaf)      = f x ⊕ g (term₂ y)
  ++-[ f , g ] (cons₁ x (cons₂ y ys) , SDCons p) =
    f x ⊕ ++-[ f , g ] (cons₂ y ys , DCons p)
  ++-[ f , g ] (cons₂ x xs , DCons p)            =
    g (term₂ x) ⊕ ++-[ f , g ] (xs , p)

  ++-[_,_]-cong : (f : A → U) → (g : Expr → U) → Congruent _≡_ _≈_ (++-[ f , g ])
  ++-[ f , g ]-cong p = Model.reflexive W (PE.cong ++-[ f , g ] p)

  open import Relation.Binary.Reasoning.Setoid Carrierₛ

  ++-[_,_]-hom : ∀ {f : A → U} {g : Expr → U}
                 → Homomorphic S Wₐ f
                 → Homomorphic |T| Θ-semigroup ⦉ n ⦊/≈ₘ  Wₐ g
                 → Homomorphic ++-algebra Wₐ ++-[ f , g ]
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf₁ x , isLeaf) ∷ (leaf₁ y , isLeaf) ∷ []) = f-hom MagmaOp.• (x ∷ y ∷ [])
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf₁ x , isLeaf) ∷ (leaf₂ y , isLeaf) ∷ []) = Model.refl W
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf₁ x , isLeaf) ∷ (cons₁ y (leaf₂ z) , SDLeaf) ∷ []) = begin
      f x ⊕ (f y ⊕ g (term₂ z))
    ≈⟨ Model.sym W (⊕-assoc (f x) (f y) (g (term₂ z))) ⟩
      (f x ⊕ f y) ⊕ g (term₂ z)
    ≈⟨ ⊕-cong (f-hom MagmaOp.• (x ∷ y ∷ [])) (Model.refl W) ⟩
      f (x • y) ⊕ g (term₂ z)
    ≡⟨⟩
      ++-[ f , g ] (cons₁ (x • y) (leaf₂ z) , SDLeaf)
    ≡⟨⟩
      ++-[ f , g ] ((leaf₁ (x • y) , isLeaf) ++ (leaf₂ z , isLeaf))
    ∎
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf₁ x , isLeaf) ∷ (cons₁ y (cons₂ z w) , SDCons p) ∷ []) = begin
      f x ⊕ (f y ⊕ (g (term₂ z) ⊕ ++-[ f , g ] (w , p)))
    ≈⟨ Model.sym W (⊕-assoc (f x) (f y) (g (term₂ z) ⊕ ++-[ f , g ] (w , p))) ⟩
      (f x ⊕ f y) ⊕ (g (term₂ z) ⊕ ++-[ f , g ] (w , p))
    ≈⟨ ⊕-cong (f-hom MagmaOp.• (x ∷ y ∷ [])) (Model.refl W) ⟩
      f (x • y) ⊕ ++-[ f , g ] ((leaf₂ z , isLeaf) ++ (w , p))
    ≡⟨⟩
      ++-[ f , g ] ((cons₁ (x • y) (leaf₂ z) , SDLeaf) ++ (w , p))
    ∎
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf₁ x , isLeaf) ∷ (cons₂ y z , DCons p) ∷ []) =
    ⊕-cong (Model.refl W) (Model.refl W)
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((leaf₂ x , isLeaf) ∷ (y , p) ∷ []) = Model.refl W
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((cons₁ x (leaf₂ y) , SDLeaf) ∷ (z , q) ∷ []) = begin
      (f x ⊕ g (term₂ y)) ⊕ ++-[ f , g ] (z , q)
    ≈⟨ ⊕-assoc (f x) (g (term₂ y)) (++-[ f , g ] (z , q)) ⟩
      f x ⊕ (g (term₂ y) ⊕ ++-[ f , g ] (z , q))
    ≡⟨⟩
      f x ⊕ ++-[ f , g ] (cons₂ y z , DCons q)
    ≡⟨⟩
      ++-[ f , g ] (cons₁ x (cons₂ y z) , SDCons q)
    ≡⟨⟩
      ++-[ f , g ] ((cons₁ x (leaf₂ y) , SDLeaf) ++ (z , q))
    ∎
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((cons₁ x (cons₂ y z) , SDCons p) ∷ (w , q) ∷ []) = begin
      (f x ⊕ (g (term₂ y) ⊕ ++-[ f , g ] (z , p))) ⊕ ++-[ f , g ] (w , q)
    ≈⟨ ⊕-assoc (f x) (g (term₂ y) ⊕ ++-[ f , g ] (z , p)) (++-[ f , g ] (w , q)) ⟩
      f x ⊕ ((g (term₂ y) ⊕ ++-[ f , g ] (z , p)) ⊕ ++-[ f , g ] (w , q))
    ≈⟨ ⊕-cong (Model.refl W) (⊕-assoc (g (term₂ y)) (++-[ f , g ] (z , p)) (++-[ f , g ] (w , q))) ⟩
      f x ⊕ (g (term₂ y) ⊕ (++-[ f , g ] (z , p) ⊕ ++-[ f , g ] (w , q)))
    ≈⟨ Model.sym W (⊕-assoc (f x) (g (term₂ y)) ((++-[ f , g ] (z , p) ⊕ ++-[ f , g ] (w , q)))) ⟩
      (f x ⊕ g (term₂ y)) ⊕ (++-[ f , g ] (z , p) ⊕ ++-[ f , g ] (w , q))
    ≈⟨ ⊕-cong (Model.refl W) (++-[ f-hom , g-hom ]-hom MagmaOp.• ((z , p) ∷ (w , q) ∷ [])) ⟩
      (f x ⊕ g (term₂ y)) ⊕ ++-[ f , g ] ((z , p) ++ (w , q))
    ≈⟨ ⊕-assoc (f x) (g (term₂ y)) (++-[ f , g ] ((z ++-raw w) , (p ++ₙ q))) ⟩
      f x ⊕ (g (term₂ y) ⊕ ++-[ f , g ] ((z , p) ++ (w , q)))
    ≡⟨⟩
      f x ⊕ ++-[ f , g ] (cons₂ y (z ++-raw w) , DCons (p ++ₙ q))
    ≡⟨⟩
      ++-[ f , g ] (cons₁ x (cons₂ y (z ++-raw w)) , SDCons (p ++ₙ q))
    ≡⟨⟩
      ++-[ f , g ] ((cons₁ x (cons₂ y z) , SDCons p) ++ (w , q))
    ∎
  ++-[_,_]-hom {f = f} {g = g} f-hom g-hom MagmaOp.•
    ((cons₂ x xs , DCons p) ∷ (y , q) ∷ []) = begin
      (g (term₂ x) ⊕ ++-[ f ,  g ] (xs , p)) ⊕ ++-[ f , g ] (y , q)
    ≈⟨ ⊕-assoc (g (term₂ x)) (++-[ f , g ] (xs , p)) (++-[ f , g ] (y , q)) ⟩
      g (term₂ x) ⊕ (++-[ f ,  g ] (xs , p) ⊕ ++-[ f , g ] (y , q))
    ≈⟨ ⊕-cong (Model.refl W) (++-[ f-hom , g-hom ]-hom MagmaOp.• ((xs , p) ∷ (y , q) ∷ [])) ⟩
      g (term₂ x) ⊕ ++-[ f , g ] (xs ++-raw y , p ++ₙ q)
    ≡⟨⟩
      ++-[ f , g ] ((cons₂ x (xs ++-raw y)) , DCons (p ++ₙ q))
    ≡⟨⟩
      ++-[ f , g ] ((cons₂ x xs , DCons p) ++ (y , q))
    ∎

  ++-[_,_]ₕ : S →ₕ Wₐ → |T| Θ-semigroup ⦉ n ⦊/≈ₘ →ₕ Wₐ → ++-algebra →ₕ Wₐ
  ++-[_,_]ₕ F G = record { h      = ++-[ f , g ]
                         ; h-cong = ++-[ f , g ]-cong
                         ; h-hom  = ++-[ f-hom , g-hom ]-hom
                         }
    where open _→ₕ_ F renaming (h to f; h-hom to f-hom)
          open _→ₕ_ G renaming (h to g; h-hom to g-hom)

  ++-[_,_]-commute₁ : ∀ {F : S →ₕ Wₐ}
                      → {G : |T| Θ-semigroup ⦉ n ⦊/≈ₘ →ₕ Wₐ}
                      → ++-[ F , G ]ₕ ∘ₕ ++-inlₕ ≡ₕ F
  ++-[_,_]-commute₁ = Model.refl W

  ++-[_,_]-commute₂ : ∀ {F : S →ₕ Wₐ}
                      → {G : |T| Θ-semigroup ⦉ n ⦊/≈ₘ →ₕ Wₐ}
                      → ++-[ F , G ]ₕ ∘ₕ ++-inrₕ ≡ₕ G
  ++-[_,_]-commute₂ {F = F} {G = G} {x = term {0} (inj₂ k) []} =
    ++-[ f , g ]-cong (PE.refl {x = ++-inr-θ k})
    where open _→ₕ_ F renaming (h to f)
          open _→ₕ_ G renaming (h to g)
  ++-[_,_]-commute₂ {F = F} {G = G} {x = term {2} (MagmaOp.•) (x ∷ y ∷ [])} = begin
      ++-[ f , g ] (subst ++-algebra ++-inr-θ (term MagmaOp.• (x ∷ y ∷ [])))
    ≈⟨ ++-[ f , g ]-cong (subst-hom ++-model ++-inr-θ MagmaOp.• (x ∷ y ∷ [])) ⟩
      ++-[ f , g ] ((subst ++-algebra ++-inr-θ x) ++ (subst ++-algebra ++-inr-θ y))
    ≈⟨
       Model.sym W (++-[ f-hom , g-hom ]-hom MagmaOp.•
         ((subst ++-algebra ++-inr-θ x) ∷ (subst ++-algebra ++-inr-θ y) ∷ []))
     ⟩
      (++-[ f , g ] (subst ++-algebra ++-inr-θ x)) ⊕ (++-[ f , g ] (subst ++-algebra ++-inr-θ y))
    ≈⟨ ⊕-cong (++-[_,_]-commute₂ {F = F} {G = G}) (++-[_,_]-commute₂ {F = F} {G = G}) ⟩
      g x ⊕ g y
    ≈⟨ g-hom MagmaOp.• (x ∷ y ∷ []) ⟩
      g (term MagmaOp.• (x ∷ y ∷ []))
    ∎
    where open _→ₕ_ F renaming (h to f; h-hom to f-hom)
          open _→ₕ_ G renaming (h to g; h-hom to g-hom; h-cong to g-cong)

  ++-[_,_]-universal : ∀ {F : S →ₕ Wₐ}
                       → {G : |T| Θ-semigroup ⦉ n ⦊/≈ₘ →ₕ Wₐ}
                       → {H : ++-algebra →ₕ Wₐ}
                       → H ∘ₕ ++-inlₕ ≡ₕ F
                       → H ∘ₕ ++-inrₕ ≡ₕ G
                       → ++-[ F , G ]ₕ ≡ₕ H
  ++-[ c₁ , c₂ ]-universal {leaf₁ x , isLeaf} = Model.sym W c₁
  ++-[ c₁ , c₂ ]-universal {leaf₂ x , isLeaf} = Model.sym W c₂
  ++-[_,_]-universal {F} {G} {H} c₁ c₂ {cons₁ x (leaf₂ y) , SDLeaf} = begin
      ++-[ f , g ] (cons₁ x (leaf₂ y) , SDLeaf)
    ≡⟨⟩
      f x ⊕ g (term₂ y)
    ≈⟨ ⊕-cong (Model.sym W c₁) (Model.sym W c₂) ⟩
      h (leaf₁ x , isLeaf) ⊕ h (leaf₂ y , isLeaf)
    ≈⟨ h-hom MagmaOp.• ((leaf₁ x , isLeaf) ∷ (leaf₂ y , isLeaf) ∷ []) ⟩
      h ((leaf₁ x , isLeaf) ++ (leaf₂ y , isLeaf))
    ≡⟨⟩
      h (cons₁ x (leaf₂ y) , SDLeaf)
    ∎
    where open _→ₕ_ F renaming (h to f; h-hom to f-hom)
          open _→ₕ_ G renaming (h to g; h-hom to g-hom)
          open _→ₕ_ H
  ++-[_,_]-universal {F} {G} {H} c₁ c₂ {cons₁ x (cons₂ y z) , SDCons p} = begin
      ++-[ f , g ] (cons₁ x (cons₂ y z) , SDCons p)
    ≡⟨⟩
      f x ⊕ (g (term₂ y) ⊕ ++-[ f , g ] (z , p))
    ≈⟨ ⊕-cong (Model.sym W c₁) (⊕-cong (Model.sym W c₂) (++-[_,_]-universal {F} {G} {H} c₁ c₂)) ⟩
      h (leaf₁ x , isLeaf) ⊕ (h (leaf₂ y , isLeaf) ⊕ h (z , p))
    ≈⟨ ⊕-cong (Model.refl W) (h-hom MagmaOp.• ((leaf₂ y , isLeaf) ∷ (z , p) ∷ [])) ⟩
      h (leaf₁ x , isLeaf) ⊕ h (cons₂ y z , DCons p)
    ≈⟨ h-hom MagmaOp.• ((leaf₁ x , isLeaf) ∷ (cons₂ y z , DCons p) ∷ []) ⟩
      h (cons₁ x (cons₂ y z) , SDCons p)
    ∎
    where open _→ₕ_ F renaming (h to f; h-hom to f-hom)
          open _→ₕ_ G renaming (h to g; h-hom to g-hom)
          open _→ₕ_ H
  ++-[_,_]-universal {F} {G} {H} c₁ c₂ {cons₂ x y , DCons p} = begin
      ++-[ f , g ] (cons₂ x y , DCons p)
    ≡⟨⟩
      g (term₂ x) ⊕ ++-[ f , g ] (y , p)
    ≈⟨ ⊕-cong (Model.sym W c₂) (++-[_,_]-universal {F} {G} {H} c₁ c₂) ⟩
      h (leaf₂ x , isLeaf) ⊕ h (y , p)
    ≈⟨ h-hom MagmaOp.• ((leaf₂ x , isLeaf) ∷ (y , p) ∷ []) ⟩
      h ((leaf₂ x , isLeaf) ++ (y , p))
    ≡⟨⟩
      h (cons₂ x y , DCons p)
    ∎
    where open _→ₕ_ F renaming (h to f; h-hom to f-hom)
          open _→ₕ_ G renaming (h to g; h-hom to g-hom)
          open _→ₕ_ H

++-isFrex : IsFreeExtension M n ++-model
++-isFrex =
  record { inl       = ++-inlₕ
         ; inr       = ++-inrₕ
         ; [_,_]     = λ {_} {_} {W} → ++-[_,_]ₕ {W = W}
         ; commute₁  = λ {_} {_} {W} {F} {G} → ++-[_,_]-commute₁ {W = W} {F = F} {G = G}
         ; commute₂  = λ {_} {_} {W} {F} {G} → ++-[_,_]-commute₂ {W = W} {F = F} {G = G}
         ; universal = λ {_} {_} {W} {F} {G} {H} → ++-[_,_]-universal {W = W} {F = F} {G = G} {H = H}
         }
