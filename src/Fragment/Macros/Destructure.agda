{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Destructure where

open import Reflection hiding (name; Type)
open import Fragment.Macros.Base

open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; zip)
open import Data.Vec using (Vec; []; _∷_; fromList)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Fragment.Equational.Theory hiding (_⦉_⦊)
open import Fragment.Equational.Model
open import Fragment.Algebra.Signature
open import Fragment.Algebra.TermAlgebra using (term)

open import Fragment.Macros.Fin using (fin)

extract-arity : Name → Name → TC ℕ
extract-arity m op
  = do τ ← inferType (def (quote Model.⟦_⟧) (vra (def m []) ∷ (vra (con op [])) ∷ []))
       α ← extract-type-arg τ
       vec-len α

⟦⟧ : Name → Name → Term
⟦⟧ m op = def (quote Model.⟦_⟧) (vra (def m []) ∷ (vra (con op [])) ∷ [])

normalised-⟦⟧ : Name → Name → TC Term
normalised-⟦⟧ m op
  = do n ← extract-arity m op
       normalise (n-ary n (apply (⟦⟧ m op) (vra (vec (debrujin n)) ∷ [])))

sig-ops : Term → TC Term
sig-ops Σ = normalise (def (quote Signature.ops) (vra Σ ∷ []))

model-sig : Term → TC Term
model-sig (def (quote Model) (Θ ∷ _ ∷ _ ∷ [])) = normalise (def (quote Theory.Σ) (Θ ∷ []))
model-sig _ = typeError (strErr "can't get signature of type that isn't" ∷ nameErr (quote Model) ∷ [])

extract-sig : Name → TC Term
extract-sig m
  = do τ ← inferType (def m [])
       model-sig τ

record Operator : Set where
  constructor operator
  field
    name : Name
    normalised : Term
    arity : ℕ

open Operator

gather-⟦⟧ : Name → TC (List Operator)
gather-⟦⟧ m
  = do Σ ← extract-sig m
       ops ← sig-ops Σ
       cs ← extract-constructors ops
       arities ← flattenTC (map (extract-arity m) cs)
       normalised-⟦⟧s ← flattenTC (map (normalised-⟦⟧ m) cs)
       return (mapList (mapList (map operator cs) normalised-⟦⟧s) arities)

mutual
  leaves-args : List Operator → List (Arg Term) → TC ℕ
  leaves-args ops [] = return 0
  leaves-args ops (vArg x ∷ xs)
    = do x' ← leaves ops x
         xs' ← leaves-args ops xs
         return (x' + xs')
  leaves-args ops (_  ∷ xs) = leaves-args ops xs

  leaves-inner : List Operator → ℕ → Term → TC ℕ
  leaves-inner ops n (var _ args)     = leaves-args ops (ekat n args)
  leaves-inner ops n (con _ args)     = leaves-args ops (ekat n args)
  leaves-inner ops n (def _ args)     = leaves-args ops (ekat n args)
  leaves-inner ops n (meta _ args)    = leaves-args ops (ekat n args)
  leaves-inner ops n (pat-lam _ args) = leaves-args ops (ekat n args)
  leaves-inner _ _ t = typeError (termErr t ∷ strErr "has no arguments" ∷ [])

  leaves : List Operator → Term → TC ℕ
  leaves ops t with findMap (λ x → prefix (arity x) (normalised x) t) arity ops
  ...             | just n  = leaves-inner ops n t
  ...             | nothing = return 1

mk-term : Term → Operator → Term
mk-term Σ (operator η _ n) =
  con (quote term) (hra Σ ∷ hra (lit (nat n)) ∷ vra (con η []) ∷ [])

mk-atom : Term → Term → Term
mk-atom Σ t =
  con (quote term) (hra Σ ∷ hra (lit (nat 0)) ∷ vra t ∷ vra (vec []) ∷ [])

mutual
  destructure-args : Term → List Operator → ℕ → List (Arg Term) → TC (List Term × ℕ)
  destructure-args Σ ops acc [] = return ([] , acc)
  destructure-args Σ ops acc (vArg x ∷ xs)
    = do (x' , acc') ← destructure Σ ops acc x
         (xs' , acc'') ← destructure-args Σ ops acc' xs
         return (x' ∷ xs' , acc'')
  destructure-args Σ ops acc (_ ∷ xs) = destructure-args Σ ops acc xs

  destructure-inner : Term → List Operator → ℕ → ℕ → Term → TC (List Term × ℕ)
  destructure-inner Σ ops n acc (var _ args)     = destructure-args Σ ops acc args
  destructure-inner Σ ops n acc (con _ args)     = destructure-args Σ ops acc args
  destructure-inner Σ ops n acc (def _ args)     = destructure-args Σ ops acc args
  destructure-inner Σ ops n acc (meta _ args)    = destructure-args Σ ops acc args
  destructure-inner Σ ops n acc (pat-lam _ args) = destructure-args Σ ops acc args
  destructure-inner _ _ _ _ t = typeError (termErr t ∷ strErr "has no arguments" ∷ [])

  destructure : Term → List Operator → ℕ → Term → TC (Term × ℕ)
  destructure Σ ops acc t
    with find (λ x → prefix (arity x) (normalised x) t) ops
  ...  | just x@(operator _ _ n)
           = do (args , acc') ← destructure-inner Σ ops n acc t
                return (apply (mk-term Σ x) (vra (vec (fromList args)) ∷ []) , acc')
  ...  | nothing = return (mk-atom Σ (con (quote inj₂) (vra (fin acc) ∷ [])) , acc + 1)

macro
  count-leaves : Name → Term → Term → TC ⊤
  count-leaves m t goal
    = do ops ← gather-⟦⟧ m
         count ← leaves ops t
         unify goal (lit (nat count))

  destruct : Name → Term → Term → TC ⊤
  destruct m t goal
    = do ops ← gather-⟦⟧ m
         count ← leaves ops t
         Σ ← extract-sig m
         let Σ' = def (quote _⦉_⦊) (vra Σ ∷ vra (lit (nat count)) ∷ [])
         (t' , _) ← destructure Σ' ops 0 t
         unify goal t'
