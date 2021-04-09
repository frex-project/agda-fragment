{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Fragment where

open import Reflection hiding (name; Type; _≟_; reduce)
open import Reflection.Term using (_≟_)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)

open import Function using (_∘_)

open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; zip; sum; concat; upTo)
open import Data.Vec using (Vec; []; _∷_; fromList)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin)

open import Fragment.Equational.Theory
open import Fragment.Equational.Model
open import Fragment.Equational.FreeExtension
open import Fragment.Algebra.Signature
open import Fragment.Algebra.TermAlgebra using (term)
open import Fragment.Algebra.FreeAlgebra using (subst)

open import Fragment.Macros.Base
open import Fragment.Macros.Fin
open import Fragment.Macros.Environment Term _≡_ {{≡-isDecEquivalence}}

extract-arity : Term → Name → TC ℕ
extract-arity m op
  = do τ ← inferType (def (quote _⟦_⟧) (vra m ∷ (vra (con op [])) ∷ []))
       α ← extract-type-arg τ
       vec-len α

⟦⟧ : Term → Name → Term
⟦⟧ m op = def (quote _⟦_⟧) (vra m ∷ (vra (con op [])) ∷ [])

normalised-⟦⟧ : Term → Name → TC Term
normalised-⟦⟧ m op
  = do n ← extract-arity m op
       normalise (n-ary n (apply (⟦⟧ m op) (vra (vec (debrujin n)) ∷ [])))

sig-ops : Term → TC Term
sig-ops Σ = normalise (def (quote Signature.ops) (vra Σ ∷ []))

model-theory : Term → TC Term
model-theory (def (quote Model) (vArg Θ ∷ _ ∷ _ ∷ [])) = normalise Θ
model-theory _ = typeError (strErr "can't get theory of type that isn't" ∷ nameErr (quote Model) ∷ [])

model-sig : Term → TC Term
model-sig (def (quote Model) (Θ ∷ _ ∷ _ ∷ [])) = normalise (def (quote Theory.Σ) (Θ ∷ []))
model-sig _ = typeError (strErr "can't get signature of type that isn't" ∷ nameErr (quote Model) ∷ [])

extract-theory : Term → TC Term
extract-theory m
  = do τ ← inferType m
       model-theory τ

extract-sig : Term → TC Term
extract-sig m
  = do τ ← inferType m
       model-sig τ

extract-carrier : Term → TC Term
extract-carrier m = normalise (def (quote ∥_∥) (vra m ∷ []))

record Operator : Set where
  constructor operator
  field
    name : Name
    normalised : Term
    arity : ℕ

open Operator

gather-⟦⟧ : Term → TC (List Operator)
gather-⟦⟧ m
  = do Σ ← extract-sig m
       ops ← sig-ops Σ
       cs ← extract-constructors ops
       arities ← listTC (map (extract-arity m) cs)
       normalised-⟦⟧s ← listTC (map (normalised-⟦⟧ m) cs)
       return (mapList (mapList (map operator cs) normalised-⟦⟧s) arities)

mk-term : Term → Operator → Term
mk-term Σ (operator η _ n) =
  con (quote term) (hra Σ ∷ hra (lit (nat n)) ∷ vra (con η []) ∷ [])

mk-atom : Term → Term → Term
mk-atom Σ t =
  con (quote term) (hra Σ ∷ hra (lit (nat 0)) ∷ vra t ∷ vra (vec []) ∷ [])

mk-injection : Term → Term → Environment ℕ → Term → Term
mk-injection frex Θ env t
  with lookup t env
...  | just n  = def (quote FX-inr) ((vra Θ) ∷ vra frex ∷ (vra (fin n)) ∷ [])
...  | nothing = def (quote FX-inl) ((vra Θ) ∷ vra frex ∷ vra t ∷ [])

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
       → Term → Term → B → TC (A × B)
fold f g m t ε
  = do ops ← gather-⟦⟧ m
       fold-acc f g ops ε t

fold-⊤ : ∀ {a} {A : Set a}
         → (Term → A)
         → (Operator → List A → A)
         → Term → Term → TC A
fold-⊤ f g m t
  = do (x , _) ← fold (λ x → λ _ → (f x , ⊤)) g m t ⊤
       return x

fold-s : ∀ {a} {A : Set a}
         → (Term → A → A)
         → Term → Term → A → TC A
fold-s f m t ε
  = do (_ , acc) ← fold (λ x → λ acc → (⊤ , f x acc)) (λ _ → λ _ → ⊤) m t ε
       return acc

leaves : Term → Term → TC ℕ
leaves = fold-⊤ (λ _ → 1) (λ _ → sum)

mutual
  isOpen-args : Term → List (Arg Term) → TC Bool
  isOpen-args τ []       = return false
  isOpen-args τ (vArg x ∷ xs)
    = do xOpen ← isOpen τ x
         xsOpen ← isOpen-args τ xs
         return (xOpen ∨ xsOpen)
  isOpen-args τ (_ ∷ xs) = isOpen-args τ xs

  isOpen : Term → Term → TC Bool
  isOpen τ (var x args)
    = do τ' ← inferType (var x args)
         if equalTypes τ τ' then return true
                            else return false
  isOpen τ (meta x args)
    = do τ' ← inferType (meta x args)
         if equalTypes τ τ' then return true
                            else return false
  isOpen τ (con c args)  = isOpen-args τ args
  isOpen τ (def f args)  = isOpen-args τ args
  isOpen τ _             = return false

open-env : Term → Term → Environment ℕ → TC (Environment ℕ)
open-env m t e = flatten (fold-s binding m t (return e))
  where binding : Term → TC (Environment ℕ) → TC (Environment ℕ)
        binding x e
          = do e' ← e
               τ ← extract-carrier m
               xOpen ← isOpen τ x
               if xOpen then return (setDefault x e' (keys e'))
                        else e

destruct : Term → Term → ℕ → TC Term
destruct m t count
  = do Σ ← extract-sig m
       let Σ' = def (quote _⦉_⦊) (vra Σ ∷ vra (lit (nat count)) ∷ [])
       (t' , _) ← fold (λ _ → λ n → (mk-atom Σ' (con (quote inj₂) (vra (fin n) ∷ [])) , n + 1))
                       (λ op → λ xs → apply (mk-term Σ' op) (vra (vec (fromList xs)) ∷ []))
                       m t 0
       return t'

environment : Term → Environment ℕ → Term → TC Term
environment m env τ
  = do η ← fin-def (keys env) τ
       let clauses = map (λ (k , v) → fin-vclause v k) env
       defineFun η clauses
       return (def η [])

direct-subst : Term → Term → Term → ℕ → TC Term
direct-subst m t τ count
  = do η ← fin-def count τ
       (clauses , _) ← fold (λ x → λ n → (fin-vclause n x ∷ [] , n + 1))
                            (λ _ → concat)
                            m t 0
       defineFun η clauses
       return (def η [])

indirect-subst : Term → Term → Term → Environment ℕ → Term → ℕ → TC Term
indirect-subst m frex Θ env t count
  = do let carrier = def (quote ∥FX∥) (vra Θ ∷ vra frex ∷ [])
       η ← fin-def count carrier
       (clauses , _) ← fold (λ x → λ n → (fin-vclause n (mk-injection frex Θ env x) ∷ [] , n + 1))
                            (λ _ → concat)
                            m t 0
       defineFun η clauses
       return (def η [])

auto-factor : Term → Term → Term → Term → Environment ℕ → Term → Term → Term → TC (Term × Term)
auto-factor m frex Σ Θ env θ t τ
  = do count ← leaves m t
       structure ← destruct m t count
       direct ← direct-subst m t τ count
       indirect ← indirect-subst m frex Θ env t count
       η ← freshName "_"
       let algebra = def (quote ∥FX∥ₐ) (vra Θ ∷ vra frex ∷ [])
       let substitution = def (quote subst) ( vra Σ
                                            ∷ vra algebra
                                            ∷ vra indirect
                                            ∷ vra structure
                                            ∷ []
                                            )
       let reduction = def (quote reduce) ( vra Θ
                                          ∷ vra frex
                                          ∷ vra θ
                                          ∷ vra substitution
                                          ∷ []
                                          )
       let prop = def (quote _≡_) ( vra reduction
                                  ∷ vra t
                                  ∷ []
                                  )
       declareDef (vra η) prop
       let f = def (quote _∘_) ( vra (def (quote reduce)
                                          ( vra Θ
                                          ∷ vra frex
                                          ∷ vra θ
                                          ∷ []))
                               ∷ vra indirect
                               ∷ []
                               )
       proof ← fin-refl count f direct
       let factorisation = def (quote factor) ( vra Θ
                                              ∷ vra frex
                                              ∷ vra direct
                                              ∷ vra indirect
                                              ∷ vra θ
                                              ∷ vra proof
                                              ∷ hra structure
                                              ∷ []
                                              )
       defineFun η (Clause.clause [] factorisation ∷ [])
       return (substitution , def η [])

macro
  fragment : Name → Term → Term → Term → Term → TC ⊤
  fragment frex m lhs rhs goal
    = do Θ ← extract-theory m
         Σ ← extract-sig m
         carrier ← extract-carrier m
         env ← open-env m lhs empty
         env' ← open-env m rhs env
         θ ← environment m env' carrier
         let model = def (quote Model.isModel) (vra m ∷ [])
         let frex = def frex ( vra model
                             ∷ vra (lit (nat (keys env')))
                             ∷ []
                             )
         (s , p) ← auto-factor m frex Σ Θ env' θ lhs carrier
         (t , q) ← auto-factor m frex Σ Θ env' θ rhs carrier
         let frag = def (quote fundamental)
                        ( vra Θ
                        ∷ vra frex
                        ∷ hra lhs
                        ∷ hra rhs
                        ∷ hra s
                        ∷ hra t
                        ∷ vra θ
                        ∷ vra p
                        ∷ vra q
                        ∷ vra (con (quote PE.refl) [])
                        ∷ []
                        )
         frag ← normalise frag
         unify goal frag
