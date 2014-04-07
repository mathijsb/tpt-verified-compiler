
module project where

-- Prelude

data nat : Set where
  zero : nat
  succ : nat -> nat


-- Types, Values and Expressions

data TyExp : Set where
  Nat  : TyExp
  Bool : TyExp

data Val : TyExp -> Set where
  True  : Val Bool
  False : Val Bool
  Zero : Val Nat 
  Succ : Val Nat -> Val Nat

data Exp : TyExp -> Set where
  val  : forall { ty } -> (v : Val ty) -> Exp ty
  plus : (e1 : Exp Nat) -> (e2 : Exp Nat) -> Exp Nat
  if   : forall { ty } -> (b : Exp Bool) -> (e1 e2 : Exp ty) -> Exp ty


-- Basic functions

_+_ : (v1 v2 : Val Nat) -> Val Nat
Zero + m = m
Succ k + m = Succ (k + m)

cond : forall {ty } -> Val Bool -> (t e : Val ty) -> Val ty
cond True t e = t
cond False t e = e

-- Eval

eval : forall { ty } -> (e : Exp ty) -> Val ty
eval (val v) = v
eval (plus e e1 ) = (eval e ) + (eval e1 )
eval (if p t e ) = cond (eval p) (eval t) (eval e )


-- Stack
data List (A : Set) : nat -> Set where
   [] : List A zero
   _::_ : {n : nat} -> A -> List A n -> List A (succ n)

data Stack : forall {n : nat} -> List TyExp n -> Set where
  empty : Stack []
  _|>_ : {n : nat} -> {t : TyExp} -> {s : List TyExp n} -> (v : Val t) -> (xs : Stack s) -> Stack (t :: s)

top : {n : nat} -> {t : TyExp} -> {s : List TyExp n} -> Stack (t :: s) -> Val t
top (v |> x) = v

-- Code
