{-# OPTIONS --universe-polymorphism #-}

module project where

open import Data.String using (String)
open import Category.Monad.State
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary using (module StrictTotalOrder)
open import Data.Maybe

--import Data.AVL.IndexedMap
--import Data.Nat.Properties using (strictTotalOrder)

import Data.AVL
import Data.AVL.IndexedMap
import Data.Nat
import Data.Nat.Properties as ℕ

-- Prelude

data nat : Set where
  zero : nat
  succ : nat -> nat

data bool : Set where
  true : bool
  false : bool

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Types, Values and Expressions

data TyExp : Set where
  Nat  : TyExp
  Bool : TyExp

data Val : TyExp -> Set where
  True  : Val Bool
  False : Val Bool
  Zero : Val Nat 
  Succ : Val Nat -> Val Nat

data List (A : Set) : nat -> Set where
   [] : List A zero
   _::_ : {n : nat} -> A -> List A n -> List A (succ n)

data Stack : forall {n : nat} -> List TyExp n -> Set where
  empty1 : Stack []
  _|>_ : {n : nat} -> {t : TyExp} -> {s : List TyExp n} -> (v : Val t) -> (xs : Stack s) -> Stack (t :: s)

top : {n : nat} -> {t : TyExp} -> {s : List TyExp n} -> Stack (t :: s) -> Val t
top (v |> x) = v


data Exp : TyExp -> Set where
  val  : forall { ty } -> (v : Val ty) -> Exp ty
  plus : (e1 : Exp Nat) -> (e2 : Exp Nat) -> Exp Nat
  if   : forall { ty } -> (b : Exp Bool) -> (e1 e2 : Exp ty) -> Exp ty
  assign : forall { ty } -> (s : String) -> (e : Exp ty) -> Exp ty
  ref : forall { ty } -> (s : String) -> Exp ty
  exprs : forall { ty n } -> List (Exp ty) n -> Exp ty

-- Basic functions

_+_ : (v1 v2 : Val Nat) -> Val Nat
Zero + m = m
Succ k + m = Succ (k + m)


cond : forall {ty } -> Val Bool -> (t e : Val ty) -> Val ty
cond True t e = t
cond False t e = e

-- Eval
--open Data.AVL.IndexedMap Data.Nat.Properties.strictTotalOrder {!!}
--open Data.AVL.IndexedMap -- (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder)
--open Data.AVL.IndexedMap

--test-tree : Map (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder)
--test-tree = {!!}

open Data.AVL (Vec String)
              (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder)
open Data.AVL.IndexedMap

test-bla : Map
test-bla = ?

{-
test : Tree -> String
test t with lookup 3 t
test t | just x = {!!}
test t | nothing = {!!} -}

{-
eval : forall { ty } -> (e : Exp ty) -> (m : Map) -> Val ty
eval (val v) env = v
eval (plus e e1 ) env = (eval e ) + (eval e1 )
eval (if p t e ) env = cond (eval p) (eval t) (eval e )
eval (assign s e) env = {!!}
eval (ref s) env = {!!}
eval (exprs []) env = {!!}
eval (exprs (x :: s)) env = {!!} -}

-- Stack


-- Code

data Code : {n k : nat} -> List TyExp n -> List TyExp k -> Set where
  skip : {n k : nat} -> {S : List TyExp n} -> {S' : List TyExp k} -> Code S S
  _++_ : {k l m : nat} -> {S0 : List TyExp k} -> {S1 : List TyExp l} -> {S2 : List TyExp m} -> Code S0 S1 -> Code S1 S2 -> Code S0 S2
  PUSH : {T : TyExp} -> {n : nat} -> {S : List TyExp n} -> Val T -> Code S (T :: S)
  ADD  : {n : nat} -> {S : List TyExp n} -> Code (Nat :: (Nat :: S)) (Nat :: S)
  IF   : {n k : nat} -> {S : List TyExp n} -> {S' : List TyExp k} -> Code S S' -> Code S S' -> Code (Bool :: S) S'  --not sure here either

exec : {n k : nat} ->{S : List TyExp n} -> {S' : List TyExp k} -> Code S S' -> Stack S -> Stack S'
exec skip s = s
exec (c ++ c₁) s = exec c₁ (exec c s)
exec (PUSH x) s = x |> s
exec ADD (v |> (v₁ |> s)) = (v + v₁) |> s
exec (IF c1 c2) (True |> s) = exec c1 s
exec (IF c1 c2) (False |> s) = exec c2 s

compile : {n : nat} -> {S : List TyExp n} -> {T : TyExp } -> Exp T -> Code S ( T :: S)
compile (val v) = PUSH v
compile (plus e e₁) = compile e₁ ++ (compile e ++ ADD)
compile (if e e₁ e₂) = compile e ++ IF (compile e₁) (compile e₂)
compile (assign s e) = {!!}
compile (ref s) = {!!}
compile (exprs s) = {!!}


-- Correct
{-
correct : {T : TyExp} -> {n : nat} -> {S : List TyExp n} -> (e : Exp T) -> (s : Stack S) -> ((eval e) |> s) ≡ (exec (compile e) s)
correct (val v) s = refl
correct (plus e e₁) s with correct e s | correct e₁ s
correct (plus e e₁) s | k | l with (exec (compile e) s) | (exec (compile e₁) s) | (eval e₁)
correct (plus e e₁) s | refl | refl | .(eval e |> s) | .(eval1 |> s) | eval1 with correct e (eval1 |> s)
... | g  with (exec (compile e) (eval1 |> s))
correct (plus e e₁) s | refl | refl | .(eval e |> s) | .(eval1 |> s) | eval1 | refl | .(eval e |> (eval1 |> s)) = refl
correct (if e e1 e2) s with correct e s
... | c with (exec (compile e) s) | (eval e)
correct (if e e1 e2) s | refl | .(True |> s) | True = correct e1 s
correct (if e e1 e2) s | refl | .(False |> s) | False = correct e2 s
correct (assign n e) s = {!!}
correct (ref n) s = {!!}
correct (exprs e) s = {!!} -}
