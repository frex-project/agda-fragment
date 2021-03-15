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

open import Fragment.Macros.Fin using (fin; fin-vclause)

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
  parse-args : ∀ {a} {A : Set a}
               → (Term → ℕ → TC A)
               → (Operator → List A → TC A)
               → List Operator → ℕ → List (Arg Term) → TC (List A × ℕ)
  parse-args f g ops acc [] = return ([] , acc)
  parse-args f g ops acc (vArg x ∷ xs)
    = do (x' , acc') ← parse-acc f g ops acc x
         (xs' , acc'') ← parse-args f g ops acc' xs
         return (x' ∷ xs' , acc'')
  parse-args f g ops acc (_ ∷ xs) = parse-args f g ops acc xs

  parse-inner : ∀ {a} {A : Set a}
                      → (Term → ℕ → TC A)
                      → (Operator → List A → TC A)
                      → List Operator → ℕ → ℕ → Term → TC (List A × ℕ)
  parse-inner f g ops n acc (var _ args)     = parse-args f g ops acc (ekat n args)
  parse-inner f g ops n acc (con _ args)     = parse-args f g ops acc (ekat n args)
  parse-inner f g ops n acc (def _ args)     = parse-args f g ops acc (ekat n args)
  parse-inner f g ops n acc (meta _ args)    = parse-args f g ops acc (ekat n args)
  parse-inner f g ops n acc (pat-lam _ args) = parse-args f g ops acc (ekat n args)
  parse-inner _ _ _ _ _ t = typeError (termErr t ∷ strErr "has no arguments" ∷ [])

  parse-acc : ∀ {a} {A : Set a}
                → (Term → ℕ → TC A)
                → (Operator → List A → TC A)
                → List Operator → ℕ → Term → TC (A × ℕ)
  parse-acc f g ops acc t
    with find (λ x → prefix (arity x) (normalised x) t) ops
  ...  | just x@(operator _ _ n)
           = do (args , acc') ← parse-inner f g ops n acc t
                ρ ← g x args
                return (ρ , acc')
  ...  | nothing = do μ ← f t acc
                      return (μ , acc + 1)

parse : ∀ {a} {A : Set a}
        → (Term → ℕ → TC A)
        → (Operator → List A → TC A)
        → Name → Term → TC A
parse f g m t
  = do ops ← gather-⟦⟧ m
       (x , _) ← parse-acc f g ops 0 t
       return x

leaves : Name → Term → TC ℕ
leaves = parse (λ _ → λ _ → return 1) (λ _ → λ xs → return (sum xs))

macro
  destruct : Name → Term → Term → TC ⊤
  destruct m t goal
    = do count ← leaves m t
         Σ ← extract-sig m
         let Σ' = def (quote _⦉_⦊) (vra Σ ∷ vra (lit (nat count)) ∷ [])
         t' ← parse (λ _ → λ n → return (mk-atom Σ' (con (quote inj₂) (vra (fin n) ∷ []))))
                    (λ op → λ xs → return (apply (mk-term Σ' op) (vra (vec (fromList xs)) ∷ [])))
                    m t
         unify goal t'

  direct-subst : Name → Term → Term → TC ⊤
  direct-subst m t goal
    = do count ← leaves m t
         carrier ← inferType t
         fin ← quoteTC (Fin count)
         let τ = pi (vra fin) (abs "n" carrier)
         η ← freshName "_"
         declareDef (vra η) τ
         clauses ← parse (λ x → λ n → return (fin-vclause n x ∷ []))
                         (λ _ → λ xs → return (concat xs))
                         m t
         defineFun η clauses
         unify goal (def η [])
