{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Destructure where

open import Reflection hiding (name; Type)
open import Fragment.Macros.Base

open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; zip; sum; concat)
open import Data.Vec using (Vec; []; _∷_; fromList)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin)

open import Fragment.Equational.Theory hiding (_⦉_⦊)
open import Fragment.Equational.Model
open import Fragment.Algebra.Signature
open import Fragment.Algebra.TermAlgebra using (term)

open import Fragment.Macros.Fin using (fin; fin-vclause; fin-def)

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

mk-term : Term → Operator → Term
mk-term Σ (operator η _ n) =
  con (quote term) (hra Σ ∷ hra (lit (nat n)) ∷ vra (con η []) ∷ [])

mk-atom : Term → Term → Term
mk-atom Σ t =
  con (quote term) (hra Σ ∷ hra (lit (nat 0)) ∷ vra t ∷ vra (vec []) ∷ [])

mutual
  fold-args : ∀ {a b} {A : Set a} {B : Set b}
               → (Term → B → A × B)
               → (Operator → List A → A)
               → List Operator → B → List (Arg Term) → TC (List A × B)
  fold-args f g ops acc [] = return ([] , acc)
  fold-args f g ops acc (vArg x ∷ xs)
    = do (x' , acc') ← fold-acc f g ops acc x
         (xs' , acc'') ← fold-args f g ops acc' xs
         return (x' ∷ xs' , acc'')
  fold-args f g ops acc (_ ∷ xs) = fold-args f g ops acc xs

  fold-inner : ∀ {a b} {A : Set a} {B : Set b}
                → (Term → B → A × B)
                → (Operator → List A → A)
                → List Operator → ℕ → B → Term → TC (List A × B)
  fold-inner f g ops n acc (var _ args)     = fold-args f g ops acc (ekat n args)
  fold-inner f g ops n acc (con _ args)     = fold-args f g ops acc (ekat n args)
  fold-inner f g ops n acc (def _ args)     = fold-args f g ops acc (ekat n args)
  fold-inner f g ops n acc (meta _ args)    = fold-args f g ops acc (ekat n args)
  fold-inner f g ops n acc (pat-lam _ args) = fold-args f g ops acc (ekat n args)
  fold-inner _ _ _ _ _ t = typeError (termErr t ∷ strErr "has no arguments" ∷ [])

  fold-acc : ∀ {a b} {A : Set a} {B : Set b}
              → (Term → B → A × B)
              → (Operator → List A → A)
              → List Operator → B → Term → TC (A × B)
  fold-acc f g ops acc t
    with find (λ x → prefix (arity x) (normalised x) t) ops
  ...  | just x@(operator _ _ n)
           = do (args , acc') ← fold-inner f g ops n acc t
                return (g x args , acc')
  ...  | nothing = return (f t acc)

fold : ∀ {a b} {A : Set a} {B : Set b}
       → (Term → B → A × B)
       → (Operator → List A → A)
       → Name → Term → B → TC A
fold f g m t ε
  = do ops ← gather-⟦⟧ m
       (x , _) ← fold-acc f g ops ε t
       return x

fold-⊤ : ∀ {a} {A : Set a}
         → (Term → A)
         → (Operator → List A → A)
         → Name → Term → TC A
fold-⊤ f g m t = fold (λ x → λ _ → (f x , ⊤)) g m t ⊤

leaves : Name → Term → TC ℕ
leaves = fold-⊤ (λ _ → 1) (λ _ → sum)

free : Name → Term → TC ℕ
free = fold-⊤ (λ { (var _ _) → 1 ; _ → 0 }) (λ _ → sum)

macro
  destruct : Name → Term → Term → TC ⊤
  destruct m t goal
    = do count ← leaves m t
         Σ ← extract-sig m
         let Σ' = def (quote _⦉_⦊) (vra Σ ∷ vra (lit (nat count)) ∷ [])
         t' ← fold (λ _ → λ n → (mk-atom Σ' (con (quote inj₂) (vra (fin n) ∷ [])) , n + 1))
                   (λ op → λ xs → apply (mk-term Σ' op) (vra (vec (fromList xs)) ∷ []))
                   m t 0
         unify goal t'

  direct-subst : Name → Term → Term → TC ⊤
  direct-subst m t goal
    = do count ← leaves m t
         carrier ← inferType t
         η ← fin-def count carrier
         clauses ← fold (λ x → λ n → (fin-vclause n x ∷ [] , n + 1))
                        (λ _ → concat)
                        m t 0
         defineFun η clauses
         unify goal (def η [])
