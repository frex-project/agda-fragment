{-# OPTIONS --without-K --safe #-}

module Fragment.Tactic.Fragment where

open import Reflection hiding (name; Type; _≟_)
open import Reflection.Term using (_≟_)

open import Level using (_⊔_)
open import Relation.Binary using (Setoid)

open import Data.Bool using (Bool; _∨_; true; false; if_then_else_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map; sum; length)
open import Data.Vec using (fromList)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; _++_)
open import Data.Maybe using (Maybe; just; nothing)

open import Fragment.Tactic.Utils

open import Fragment.Equational.Theory
open import Fragment.Equational.Model
open import Fragment.Equational.FreeExtension hiding (reduce)
open import Fragment.Algebra.Signature
import Fragment.Algebra.Free as Free

read-goal : List (Arg Term) → TC (Term × List (Arg Term))
read-goal (vArg x ∷ xs) = return (x , xs)
read-goal (_ ∷ xs)      = read-goal xs
read-goal []            = typeError (strErr "failed to read goal" ∷ [])

read-goals : List (Arg Term) → TC (Term × Term)
read-goals xs = do (fst , xs) ← read-goal xs
                   (snd , _) ← read-goal xs
                   return (fst , snd)

extract-goals : Term → TC (Term × Term)
extract-goals (var _ args)  = read-goals args
extract-goals (con _ args)  = read-goals args
extract-goals (def _ args)  = read-goals args
extract-goals (meta _ args) = read-goals args
extract-goals t             =
  typeError (strErr "can't read goals from" ∷ termErr t ∷ [])

record Operator : Set where
  constructor operator
  field
    name       : Name
    normalised : Term
    arity      : ℕ

open Operator

record CoreCtx : Set where
  field
    signature : Term
    theory    : Term
    model     : Term
    carrier   : Term
    frex      : Term

record GlobalCtx : Set where
  field
    core      : CoreCtx
    operators : List Operator

    telescope : List (Arg String)
    lhs       : Term
    rhs       : Term

  open CoreCtx core public

pattern modelType Θ a ℓ = def (quote Model) (vArg Θ ∷ hArg a ∷ hArg ℓ ∷ [])

ctx : Name → Term → Term → TC GlobalCtx
ctx frex model goal
  = do τ ← inferType model
       γ ← inferType goal

       signature ← extract-Σ τ
       theory ← extract-Θ τ
       carrier ← normalise (def (quote ∥_∥) (vra theory ∷ vra model ∷ []))

       let core = record { signature = signature
                         ; theory    = theory
                         ; model     = model
                         ; carrier   = carrier
                         ; frex      = def frex []
                         }

       operators ← extract-ops core

       (inner , telescope) ← strip-telescope γ
       (lhs , rhs) ← extract-goals inner

       return (record { core      = core
                      ; operators = operators
                      ; telescope = telescope
                      ; lhs       = lhs
                      ; rhs       = rhs
                      })

  where modelErr : ∀ {a} {A : Set a} → Term → String → TC A
        modelErr t err =
          typeError ( termErr t
                    ∷ strErr "isn't a"
                    ∷ nameErr (quote Model)
                    ∷ strErr ("(" ++ err ++ ")")
                    ∷ []
                    )

        extract-Σ : Term → TC Term
        extract-Σ (modelType Θ _ _) = normalise (def (quote Theory.Σ) (vra Θ ∷ []))
        extract-Σ t                 = modelErr t "when extracting the signature"

        extract-Θ : Term → TC Term
        extract-Θ (modelType Θ _ _) = normalise Θ
        extract-Θ t                 = modelErr t "when extracting the theory"

        extract-arity : CoreCtx → Name → TC ℕ
        extract-arity ctx op
          = do τ ← inferType (def (quote _⟦_⟧_)
                                  ( vra (CoreCtx.theory ctx)
                                  ∷ vra (CoreCtx.model ctx)
                                  ∷ vra (con op [])
                                  ∷ []
                                  ))
               α ← extract-type-arg τ
               vec-len α

        extract-interp : CoreCtx → Name → ℕ → TC Term
        extract-interp ctx op arity
          = do let t = def (quote _⟦_⟧_)
                           ( vra (CoreCtx.theory ctx)
                           ∷ vra (CoreCtx.model ctx)
                           ∷ vra (con op [])
                           ∷ []
                           )
               normalise (n-ary arity (apply t (vra (vec (debrujin arity)) ∷ [])))

        extract-ops : CoreCtx → TC (List Operator)
        extract-ops ctx
          = do ops ← normalise (def (quote ops) (vra (CoreCtx.signature ctx) ∷ []))
               symbols ← extract-constructors ops
               arities ← listTC (map (extract-arity ctx) symbols)
               interps ← listTC (mapList (map (extract-interp ctx) symbols) arities)
               return (mapList (mapList (map operator symbols) interps) arities)

record FoldCtx {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor foldCtx
  field
    global : GlobalCtx

    f : Term → B → A × B
    g : Operator → List A → A
    ε : B

  open GlobalCtx global public

mutual

  map-fold : ∀ {a b} {A : Set a} {B : Set b}
             → FoldCtx A B → List (Arg Term) → B → TC (List A × B)
  map-fold ctx [] acc = return ([] , acc)
  map-fold ctx (vArg x ∷ xs) acc
    = do (x , acc) ← fold-acc ctx x acc
         (xs , acc) ← map-fold ctx xs acc
         return (x ∷ xs , acc)
  map-fold ctx (_ ∷ xs) acc = map-fold ctx xs acc

  fold-inner : ∀ {a b} {A : Set a} {B : Set b}
                → FoldCtx A B → Operator → Term → B → TC (List A × B)
  fold-inner ctx op (var _ args)     acc = map-fold ctx (ekat (arity op) args) acc
  fold-inner ctx op (con _ args)     acc = map-fold ctx (ekat (arity op) args) acc
  fold-inner ctx op (def _ args)     acc = map-fold ctx (ekat (arity op) args) acc
  fold-inner ctx op (meta _ args)    acc = map-fold ctx (ekat (arity op) args) acc
  fold-inner ctx op (pat-lam _ args) acc = map-fold ctx (ekat (arity op) args) acc
  fold-inner _ _ t _ = typeError (termErr t ∷ strErr "has no arguments" ∷ [])

  fold-acc : ∀ {a b} {A : Set a} {B : Set b} → FoldCtx A B → Term → B → TC (A × B)
  fold-acc ctx t acc
    = do op? ← find (λ x → prefix (arity x) (normalised x) t) (FoldCtx.operators ctx)
         resolve op?
    where resolve : Maybe Operator → TC _
          resolve (just op)
            = do (args , acc) ← fold-inner ctx op t acc
                 return ((FoldCtx.g ctx) op args , acc)
          resolve nothing = return ((FoldCtx.f ctx) t acc)

fold : ∀ {a b} {A : Set a} {B : Set b} → FoldCtx A B → Term → TC (A × B)
fold ctx t = fold-acc ctx t (FoldCtx.ε ctx)

fold-⊤ : ∀ {a} {A : Set a} → GlobalCtx
         → (Term → A) → (Operator → List A → A) → Term → TC A
fold-⊤ ctx f g t
  = do (x , _) ← fold (foldCtx ctx (λ x _ → (f x , tt)) g tt) t
       return x

accumulate : ∀ {a} {A : Set a} → GlobalCtx
             → (Term → A → A) → A → Term → TC A
accumulate ctx f ε t
  = do (_ , acc) ← fold (foldCtx ctx (λ x acc → (tt , f x acc)) (λ _ _ → tt) ε) t
       return acc

leaves : GlobalCtx → Term → TC ℕ
leaves ctx = fold-⊤ ctx (λ _ → 1) (λ _ → sum)

mutual
  argsOpen : Term → List (Arg Term) → TC Bool
  argsOpen τ [] = return false
  argsOpen τ (vArg x ∷ xs)
    = do head ← isOpen τ x
         tail ← argsOpen τ xs
         return (head ∨ tail)
  argsOpen τ (_ ∷ xs) = argsOpen τ xs

  isOpen : Term → Term → TC Bool
  isOpen τ t@(var _ _)  = hasType τ t
  isOpen τ t@(meta _ _) = hasType τ t
  isOpen τ (con c args) = argsOpen τ args
  isOpen τ (def f args) = argsOpen τ args
  isOpen τ unknown      = return true
  isOpen τ _            = return false

findOpen : GlobalCtx → List Term → Term → TC (List Term)
findOpen ctx ε t = flatten (accumulate ctx binding (return ε) t)
  where binding : Term → TC (List Term) → TC (List Term)
        binding t env
          = do env ← env
               let τ = CoreCtx.carrier (GlobalCtx.core ctx)
               open? ← isOpen τ t
               if open? then return (insert env t)
                        else return env

buildSyntax : GlobalCtx → List Term → Term → TC Term
buildSyntax ctx env t = fold-⊤ ctx buildInj buildTerm t
  where bt : Term
        bt = def (quote Free.BT)
                 ( vra (GlobalCtx.signature ctx)
                 ∷ vra (GlobalCtx.carrier ctx)
                 ∷ vra (lit (nat (length env)))
                 ∷ []
                 )

        buildAtom : Term → Term
        buildAtom t =
          con (quote Free.Term.atom)
              ( hra (GlobalCtx.signature ctx)
              ∷ hra unknown
              ∷ hra bt
              ∷ vra t
              ∷ []
              )

        buildDyn : ℕ → Term
        buildDyn n =
          con (quote Free.BT.dyn)
              ( hra (GlobalCtx.signature ctx)
              ∷ hra unknown
              ∷ hra (GlobalCtx.carrier ctx)
              ∷ hra (lit (nat (length env)))
              ∷ vra (fin n)
              ∷ []
              )

        buildSta : Term → Term
        buildSta t =
          con (quote Free.BT.sta)
              ( hra (GlobalCtx.signature ctx)
              ∷ hra unknown
              ∷ hra (GlobalCtx.carrier ctx)
              ∷ hra (lit (nat (length env)))
              ∷ vra t
              ∷ []
              )

        buildInj : Term → Term
        buildInj t with indexOf env t
        ...           | just n  = buildAtom (buildDyn n)
        ...           | nothing = buildAtom (buildSta t)

        buildTerm : Operator → List Term → Term
        buildTerm op xs =
          con (quote Free.Term.term)
               ( hra (GlobalCtx.signature ctx)
               ∷ hra unknown
               ∷ hra bt
               ∷ hra (lit (nat (arity op)))
               ∷ vra (con (name op) [])
               ∷ vra (vec (fromList xs))
               ∷ []
               )

environment : List Term → Term
environment env = vec (fromList env)

macro
  fragment : Name → Term → Term → TC ⊤
  fragment frex model goal
    = do ctx ← ctx frex model goal
         env ← findOpen ctx [] (GlobalCtx.lhs ctx)
         env ← findOpen ctx env (GlobalCtx.rhs ctx)
         lhs ← buildSyntax ctx env (GlobalCtx.lhs ctx)
         rhs ← buildSyntax ctx env (GlobalCtx.rhs ctx)
         let n = length env
         let frex = def (quote FreeExtension._[_])
                        ( hra (GlobalCtx.theory ctx)
                        ∷ vra (GlobalCtx.frex ctx)
                        ∷ vra (GlobalCtx.model ctx)
                        ∷ vra (lit (nat n))
                        ∷ []
                        )
         let setoid = def (quote ∥_∥/≈)
                          ( hra (GlobalCtx.theory ctx)
                          ∷ vra frex
                          ∷ []
                          )
         let p = def (quote Setoid.refl) (vra setoid ∷ [])
         let frexify = def (quote frexify)
                           ( vra (GlobalCtx.theory ctx)
                           ∷ vra (GlobalCtx.frex ctx)
                           ∷ vra (GlobalCtx.model ctx)
                           ∷ vra (vec (fromList env))
                           ∷ hra lhs
                           ∷ hra rhs
                           ∷ vra p
                           ∷ []
                           )
         frexify ← restore-telescope (GlobalCtx.telescope ctx) frexify
         unify frexify goal
