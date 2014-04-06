module project where

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
{-
NOT SURE ABOUT HOW TO IMPLEMENT THIS PART
data List : Set -> Set where
   [] : forall s -> List s
   _::_ : forall {s} -> s -> List s -> List s

data Stack : Set where
  empty : Stack
  _|>_ : TyExp -> Stack -> Stack

top : Stack -> TyExp
top empty = {!!}
top (x |> s) = {!!}
-}
