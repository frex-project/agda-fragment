{-# OPTIONS --without-K --safe #-}

module Fragment.Tactic.Utils where

open import Reflection hiding (name; Type; _≟_)
open import Reflection.Term using (_≟_)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Nat.Show using (show)
open import Data.String using (String) renaming (_++_ to _⟨S⟩_)
open import Data.List using (List; []; _∷_; _++_; drop; take; reverse)
open import Data.Vec using (Vec; []; _∷_; map; toList)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary using (yes; no; _because_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

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

find : ∀ {a} {A : Set a} → (A → TC Bool) → List A → TC (Maybe A)
find p [] = return nothing
find p (x ∷ xs)
  = do p? ← p x
       if p? then return (just x)
             else find p xs

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

equalTypes : Term → Term → Bool
equalTypes τ τ' with τ ≟ τ'
...                | yes _ = true
...                | _     = false

flatten : ∀ {a} {A : Set a} → TC (TC A) → TC A
flatten x
  = do x' ← x
       x'

listTC : ∀ {a} {A : Set a} → List (TC A) → TC (List A)
listTC []       = return []
listTC (x ∷ xs)
  = do x' ← x
       xs' ← listTC xs
       return (x' ∷ xs')

n-ary : ∀ (n : ℕ) → Term → Term
n-ary zero body    = body
n-ary (suc n) body = λ⦅ "x" ⟨S⟩ show n ⦆→ (n-ary n body)

debrujin : ∀ (n : ℕ) → Vec Term n
debrujin zero    = []
debrujin (suc n) = (var n []) ∷ debrujin n

η-convert : ∀ (n : ℕ) → Term → TC Term
η-convert n t = runSpeculative inner
  where inner : TC (Term × Bool)
        inner
          = do t ← normalise (n-ary n (apply t (toList (map vra (debrujin n)))))
               return (t , false)

prefix : ℕ → Term → Term → TC Bool
prefix n x y
  = do y ← catchTC (η-convert n (unapply y n)) (return y)
       let (b because _) = x ≟ y
       return b

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

fin : ℕ → Term
fin zero    = con (quote Fin.zero) []
fin (suc n) = con (quote Fin.suc) (vra (fin n) ∷ [])

vec : ∀ {n : ℕ} → Vec Term n → Term
vec []       = con (quote Vec.[]) []
vec (x ∷ xs) = con (quote Vec._∷_) (vra x ∷ vra (vec xs) ∷ [])

vec-len : Term → TC ℕ
vec-len (def (quote Vec) (_ ∷ _ ∷ (arg _ n) ∷ [])) = unquoteTC n
vec-len t = typeError (termErr t ∷ strErr "isn't a" ∷ nameErr (quote Vec) ∷ [])

panic : ∀ {a} {A : Set a} → Term → TC A
panic x = typeError (termErr x ∷ [])

strip-telescope : Term → TC (Term × List (Arg String))
strip-telescope (pi (vArg _) (abs s x))
  = do (τ , acc) ← strip-telescope x
       return (τ , vra s ∷ acc)
strip-telescope (pi (hArg _) (abs s x))
  = do (τ , acc) ← strip-telescope x
       return (τ , hra s ∷ acc)
strip-telescope (pi _ _) =
  typeError (strErr "no support for irrelevant goals" ∷ [])
strip-telescope t        = return (t , [])

restore-telescope : List (Arg String) → Term → TC Term
restore-telescope [] t = return t
restore-telescope (vArg x ∷ xs) t
  = do t ← restore-telescope xs t
       return (λ⦅ x ⦆→ t)
restore-telescope (hArg x ∷ xs) t
  = do t ← restore-telescope xs t
       return (λ⦃ x ⦄→ t)
restore-telescope (_ ∷ _) _ =
  typeError (strErr "no support for irrelevant goals" ∷ [])

hasType : Term → Term → TC Bool
hasType τ t = runSpeculative inner
  where inner = do τ' ← inferType t
                   return (equalTypes τ τ' , false)

insert : List Term → Term → List Term
insert [] n       = n ∷ []
insert (x ∷ xs) n with x ≟ n
...                  | yes _ = x ∷ xs
...                  | no _  = x ∷ insert xs n

indexOf : List Term → Term → Maybe ℕ
indexOf [] t = nothing
indexOf (x ∷ xs) t with x ≟ t | indexOf xs t
...                   | yes _ | _       = just 0
...                   | no _  | just n  = just (suc n)
...                   | no _  | nothing = nothing
