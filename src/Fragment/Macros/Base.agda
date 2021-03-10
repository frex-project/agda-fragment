{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Base where

open import Reflection hiding (name; Type; _≟_)
open import Reflection.Term using (_≟_)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.String using (String) renaming (_++_ to _⟨S⟩_)
open import Data.List using (List; []; _∷_; _++_; drop; take; reverse)
open import Data.Vec using (Vec; []; _∷_; map; toList)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)

vra : ∀ {a} {A : Set a} → A → Arg A
vra = arg (arg-info visible relevant)

hra : ∀ {a} {A : Set a} → A → Arg A
hra = arg (arg-info hidden relevant)

infixr 5 λ⦅_⦆→_ λ⦃_⦄→_

λ⦅_⦆→_ : String → Term → Term
λ⦅ x ⦆→ body = lam visible (abs x body)

λ⦃_⦄→_ : String → Term → Term
λ⦃ x ⦄→ body = lam hidden (abs x body)

constructors : Definition → List Name
constructors (data-type _ cs) = cs
constructors _                = []

apply : Term → List (Arg Term) → Term
apply (var x xs) args      = var x (xs ++ args)
apply (con x xs) args      = con x (xs ++ args)
apply (def x xs) args      = def x (xs ++ args)
apply (meta x xs) args     = meta x (xs ++ args)
apply (pat-lam cs xs) args = pat-lam cs (xs ++ args)
apply x _                  = x

prod : ∀ {a} {A : Set a} → ℕ → List A → List A
prod n xs = reverse (drop n (reverse xs))

ekat : ∀ {a} {A : Set a} → ℕ → List A → List A
ekat n xs = reverse (take n (reverse xs))

findMap : ∀ {a b} {A : Set a} {B : Set b}
          → (A → Bool) → (A → B) → List A → Maybe B
findMap p f []       = nothing
findMap p f (x ∷ xs) = if p x then just (f x) else findMap p f xs

find : ∀ {a} {A : Set a} → (A → Bool) → List A → Maybe A
find p = findMap p (λ x → x)

mapList : ∀ {a b} {A : Set a} {B : Set b}
          → List (A → B) → List A → List B
mapList [] _              = []
mapList _ []              = []
mapList (f ∷ fs) (x ∷ xs) = f x ∷ mapList fs xs

unapply : Term → ℕ → Term
unapply (var x args) n      = var x (prod n args)
unapply (con x args) n      = con x (prod n args)
unapply (def x args) n      = def x (prod n args)
unapply (meta x args) n     = meta x (prod n args)
unapply (pat-lam cs args) n = pat-lam cs (prod n args)
unapply x _                 = x

flattenTC : ∀ {a} {A : Set a} → List (TC A) → TC (List A)
flattenTC []       = return []
flattenTC (x ∷ xs)
  = do x' ← x
       xs' ← flattenTC xs
       return (x' ∷ xs')

n-ary : ∀ (n : ℕ) → Term → Term
n-ary zero body    = body
n-ary (suc n) body = λ⦅ "x" ⟨S⟩ show n ⦆→ (n-ary n body)

debrujin : ∀ (n : ℕ) → Vec Term n
debrujin zero    = []
debrujin (suc n) = (var n []) ∷ debrujin n

η-convert : ∀ (n : ℕ) → Term → Term
η-convert n t = n-ary n (apply t (toList (map vra (debrujin n))))

prefix : ℕ → Term → Term → Bool
prefix n x y with x ≟ η-convert n (unapply y n)
...             | yes _ = true
...             | no _  = false

extract-type-arg : Term → TC Term
extract-type-arg (pi (arg _ x) _) = return x
extract-type-arg x                = typeError (termErr x ∷ strErr "isn't a pi type" ∷ [])

extract-name : Term → TC Name
extract-name (def x _) = return x
extract-name x         = typeError (termErr x ∷ strErr "isn't an application of a definition" ∷ [])

extract-definition : Term → TC Definition
extract-definition x
  = do x' ← normalise x
       η ← extract-name x'
       getDefinition η

extract-constructors : Term → TC (List Name)
extract-constructors x
  = do δ ← extract-definition x
       return (constructors δ)

vec : ∀ {n : ℕ} → Vec Term n → Term
vec []       = con (quote Vec.[]) []
vec (x ∷ xs) = con (quote Vec._∷_) (vra x ∷ vra (vec xs) ∷ [])

vec-len : Term → TC ℕ
vec-len (def (quote Vec) (_ ∷ _ ∷ (arg _ n) ∷ [])) = unquoteTC n
vec-len _ = typeError (strErr "can't get length of type that isn't" ∷ nameErr (quote Vec) ∷ [])

panic : ∀ {a} {A : Set a} → Term → TC A
panic x = typeError (termErr x ∷ [])
