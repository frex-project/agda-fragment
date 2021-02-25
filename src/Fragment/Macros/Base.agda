{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Base where

open import Reflection hiding (name; Type)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (show)
open import Data.List using (List; []; _∷_; sum)
open import Data.Vec using (Vec; []; _∷_; map; toList)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

vra : ∀ {a} {A : Set a} → A → Arg A
vra = arg (arg-info visible relevant)

hra : ∀ {a} {A : Set a} → A → Arg A
hra = arg (arg-info hidden relevant)

infixr 5 λ⦅_⦆→_

λ⦅_⦆→_ : String → Term → Term
λ⦅ x ⦆→ body = lam visible (abs x body)

λ⦃_⦄→_ : String → Term → Term
λ⦃ x ⦄→ body = lam hidden (abs x body)

constructors : Definition → List Name
constructors (data-type _ cs) = cs
constructors _                = []

finPat : ∀ {n : ℕ} → Fin n → Pattern
finPat zero    = Pattern.con (quote Fin.zero) []
finPat (suc n) = Pattern.con (quote Fin.suc) (vra (finPat n) ∷ [])

finClause : ∀ {n : ℕ} → Fin n → Term → Clause
finClause n body = Clause.clause (hra (finPat n) ∷ []) body

allFin : ∀ (n : ℕ) → Vec (Fin n) n
allFin zero    = []
allFin (suc n) = zero ∷ map suc (allFin n)

macro
  fin-refl : ∀ {a} {A : Set a}
             → (n : ℕ) → (Fin n → A) → (Fin n → A)
             → Term → TC ⊤
  fin-refl {a} {A} n f g goal
    = do τ ← quoteTC (∀ {x : Fin n} → f x ≡ g x)
         η ← freshName "_"
         declareDef (vra η) τ
         defineFun η (toList (map (λ (m : Fin n) → finClause m (con (quote PE.refl) [])) (allFin n)))
         unify goal (def η [])

open import Fragment.Equational.Theory
open import Fragment.Equational.Model
open import Fragment.Algebra.Signature

len : Term → TC ℕ
len (def (quote Vec) (_ ∷ _ ∷ (arg _ n) ∷ [])) = unquoteTC n
len _ = typeError (strErr "can't get length of type that isn't" ∷ nameErr (quote Vec) ∷ [])

typeArg : Term → TC Term
typeArg (pi (arg _ x) _) = return x
typeArg _                = typeError []

interp : Name → Name → Term
interp m op = def (quote Model.⟦_⟧) (vra (def m []) ∷ (vra (con op [])) ∷ [])

arity : Name → Name → TC ℕ
arity m op
  = do τ ← inferType (interp m op)
       α ← typeArg τ
       len α

n-ary : ∀ (n : ℕ) → Term → Term
n-ary zero body    = body
n-ary (suc n) body = λ⦅ "x" ++ show n ⦆→ (n-ary n body)

vec : ∀ {n : ℕ} → Vec Term n → Term
vec []       = con (quote Vec.[]) []
vec (x ∷ xs) = con (quote Vec._∷_) (vra x ∷ vra (vec xs) ∷ [])

{-
apply : Name → Name → TC Term
apply m op
  = do n ← arity m op
       return (n-ary n (call ({!!})))
  where call : Term → Term
        call term = def (quote Model.⟦_⟧) (vra (def m []) ∷ (vra (con op [])) ∷ (vra term) ∷ [])

macro
  interpret : Name → Name → Term → TC ⊤
  interpret m op goal = {!!}

  {-
  operators : TC (List Name)
  operators = do δ ← getDefinition (quote ops)
                 return {!!}
  -}
-}
