{-# OPTIONS --without-K --safe #-}

module Fragment.Macros.Destructure where

open import Reflection hiding (name; Type)
open import Fragment.Macros.Base

open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; zip)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; proj₁; proj₂; _,_)

open import Fragment.Equational.Theory
open import Fragment.Equational.Model
open import Fragment.Algebra.Signature

arity : Name → Name → TC ℕ
arity m op
  = do τ ← inferType (def (quote Model.⟦_⟧) (vra (def m []) ∷ (vra (con op [])) ∷ []))
       α ← extract-type-arg τ
       vec-len α

⟦⟧ : Name → Name → Term
⟦⟧ m op = def (quote Model.⟦_⟧) (vra (def m []) ∷ (vra (con op [])) ∷ [])

normalised-⟦⟧ : Name → Name → TC Term
normalised-⟦⟧ m op
  = do n ← arity m op
       normalise (n-ary n (apply (⟦⟧ m op) (vra (vec (debrujin n)) ∷ [])))

sig-ops : Term → TC Term
sig-ops Σ = normalise (def (quote Signature.ops) (vra Σ ∷ []))

model-sig : Term → TC Term
model-sig (def (quote Model) (Θ ∷ _ ∷ _ ∷ [])) = normalise (def (quote Theory.Σ) (Θ ∷ []))
model-sig _ = typeError (strErr "can't get signature of type that isn't" ∷ nameErr (quote Model) ∷ [])

gather-⟦⟧ : Name → TC (List (Term × ℕ))
gather-⟦⟧ m
  = do τ ← inferType (def m [])
       Σ ← model-sig τ
       ops ← sig-ops Σ
       cs ← extract-constructors ops
       arities ← flattenTC (map (arity m) cs)
       normalised-⟦⟧s ← flattenTC (map (normalised-⟦⟧ m) cs)
       return (zip normalised-⟦⟧s arities)

mutual
  leaves-args : List (Term × ℕ) → List (Arg Term) → TC ℕ
  leaves-args ops [] = return 0
  leaves-args ops (vArg x ∷ xs)
    = do x' ← leaves ops x
         xs' ← leaves-args ops xs
         return (x' + xs')
  leaves-args ops (_  ∷ xs) = leaves-args ops xs

  leaves-inner : List (Term × ℕ) → ℕ → Term → TC ℕ
  leaves-inner ops n (var _ args)     = leaves-args ops (ekat n args)
  leaves-inner ops n (con _ args)     = leaves-args ops (ekat n args)
  leaves-inner ops n (def _ args)     = leaves-args ops (ekat n args)
  leaves-inner ops n (meta _ args)    = leaves-args ops (ekat n args)
  leaves-inner ops n (pat-lam _ args) = leaves-args ops (ekat n args)
  leaves-inner _ _ t = typeError (termErr t ∷ strErr "has no arguments" ∷ [])

  leaves : List (Term × ℕ) → Term → TC ℕ
  leaves ops t with findMap (λ x → prefix (proj₂ x) (proj₁ x) t) proj₂ ops
  ...             | just n  = leaves-inner ops n t
  ...             | nothing = return 1

macro
  count-leaves : Name → Term → Term → TC ⊤
  count-leaves m t goal
    = do ops ← gather-⟦⟧ m
         count ← leaves ops t
         unify goal (lit (nat count))
