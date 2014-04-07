
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

-- Should list have it's length in the type?
data List (A : Set) : Set where
   [] : List A
   _::_ : A -> List A -> List A

data Stack : List TyExp -> Set where
  empty : Stack []
  _|>_ : {ty : TyExp } -> { s : List TyExp } -> (v : Val ty ) -> (st : Stack s) -> Stack s

top : {ty : TyExp } -> { s : List TyExp } -> Stack s -> Val ty
top empty = {!!}  -- we don't want this case, to prevent stack underflow!
top (v |> x) = {!!}
