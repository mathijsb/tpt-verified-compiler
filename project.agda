
module project where

open import Data.Bool
open import Data.Vec
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Reflection
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data TyExp : Set where
  TyNat  : TyExp
  TyBool : TyExp

data Val : TyExp -> Set where
  nat : ℕ -> Val TyNat
  bool : Bool -> Val TyBool

data Exp : ℕ -> TyExp -> Set where
  val  : forall {t₁} -> (v : Val t₁) -> Exp zero t₁
  plus : (e₁ : Exp zero TyNat) -> (e₂ : Exp zero TyNat) -> Exp zero TyNat
  if   : forall {t} -> (b : Exp zero TyBool) -> (e₁ e₂ : Exp zero t) -> Exp zero t
  var  : forall {n} -> Fin n -> Exp n TyBool
  let₁ : forall {n t} -> Exp n TyBool -> Exp (suc n) t -> Exp n t

eval : forall { t₁ n } -> (e : Exp n t₁) -> Vec (Val TyBool) n -> Val t₁
eval (val v) env = v
eval (plus e₁ e₂) env with (eval e₁ env) | (eval e₂ env)
eval (plus e₁ e₂) env | nat x₁ | nat x₂ = nat (x₁ + x₂)
eval (if e e₁ e₂) env with (eval e env) 
eval (if e e₁ e₂) env | bool true = eval e₁ env
eval (if e e₁ e₂) env | bool false = eval e₂ env
eval (var x) env = lookup x env
eval (let₁ e₁ e₂) env = eval e₂ ((eval e₁ env) ∷ env) -- eval e₂ ((eval e₁ env) ∷ env)

data Code : {n k : ℕ} -> Vec TyExp n -> Vec TyExp k -> Set where
  skip  : {n k : ℕ} -> {S : Vec TyExp n} -> {S' : Vec TyExp k} -> Code S S
  _++₁_ : {k l m : ℕ} -> {S0 : Vec TyExp k} -> {S1 : Vec TyExp l} -> {S2 : Vec TyExp m} -> Code S0 S1 -> Code S1 S2 -> Code S0 S2
  PUSH  : {T : TyExp} -> {n : ℕ} -> {S : Vec TyExp n} -> Val T -> Code S (T ∷ S)
  ADD   : {n : ℕ} -> {S : Vec TyExp n} -> Code (TyNat ∷ (TyNat ∷ S)) (TyNat ∷ S)
  IF    : {n k : ℕ} -> {S : Vec TyExp n} -> {S' : Vec TyExp k} -> Code S S' -> Code S S' -> Code (TyBool ∷ S) S'
  LDS   : {n : ℕ} {S : Vec TyExp n} {t : TyExp} -> ℕ -> Code S (t ∷ S)
  POP   : {n : ℕ} {S : Vec TyExp n} {t₁ t₂ : TyExp} -> Code (t₁ ∷ (t₂ ∷ S)) (t₁ ∷ S) -- Bit ugly, should be STS instead

data Stack : forall {n : ℕ} -> Vec TyExp n -> Set where
  empty : Stack []
  _|>_ : {n : ℕ} -> {t : TyExp} -> {s : Vec TyExp n} -> (v : Val t) -> (xs : Stack s) -> Stack (t ∷ s)

top : {n : ℕ} -> {t : TyExp} -> {s : Vec TyExp n} -> Stack (t ∷ s) -> Val t
top (v |> x) = v

exec : {n k : ℕ} -> {S : Vec TyExp n} -> {S' : Vec TyExp k} -> Code S S' -> Stack S -> Stack S'
exec skip s = s
exec (c ++₁ c₁) s = exec c₁ (exec c s)
exec (PUSH x) s = x |> s
exec ADD (nat x |> (nat x₁ |> s)) = nat (x + x₁) |> s
exec (IF c1 c2) (bool true |> s) = exec c1 s
exec (IF c1 c2) (bool false |> s) = exec c2 s -- (True |> s) = exec c1 s
exec (LDS n) x = {!!}
exec POP (v |> (v₁ |> x)) = v |> x

compile : {n n2 : ℕ} -> {S : Vec TyExp n} -> {T : TyExp } -> Exp n2 T -> Code S ( T ∷ S)
compile (val v) = PUSH v
compile (plus e e₁) = compile e₁ ++₁ (compile e ++₁ ADD)
compile (if e e₁ e₂) = compile e ++₁ IF (compile e₁) (compile e₂)
compile (var i) = LDS 1 -- PUSH (bool true)
compile (let₁ e₁ e₂) = (compile e₁ ++₁ compile e₂) ++₁ POP

correct : {T : TyExp} -> {n n₁ : ℕ} -> {S : Vec TyExp n} -> (e : Exp n₁ T) -> (s : Stack S) ->  (env : Vec (Val TyBool) n₁) -> ((eval e env) |> s) ≡ (exec (compile e) s)
correct (val v) s env = refl
correct (plus e e₁) s env with correct e s env | correct e₁ s env
... | p1 | p2 with (exec (compile e) s) | (exec (compile e₁) s) | (eval e₁ env)
correct (plus e e₁) s env | refl | refl | .(eval e env |> s) | .(v1 |> s) | v1 = {!!}
correct (if e e1 e2) s env with correct e s env
... | c with (exec (compile e) s) | (eval e env)
correct (if e e1 e2) s env | refl | .(bool true |> s) | bool true = correct e1 s env
correct (if e e1 e2) s env | refl | .(bool false |> s) | bool false = correct e2 s env
correct (var x) s env = {!!}
correct (let₁ e e₁) s env = {!!}

{-
correct (val v) s = refl
correct (plus e e₁) s with correct e s | correct e₁ s
correct (plus e e₁) s | k | l with (exec (compile e) s) | (exec (compile e₁) s) | (eval e₁)
correct (plus e e₁) s | refl | refl | .(eval e |> s) | .(eval1 |> s) | eval1 with correct e (eval1 |> s)
... | g  with (exec (compile e) (eval1 |> s))
correct (plus e e₁) s | refl | refl | .(eval e |> s) | .(eval1 |> s) | eval1 | refl | .(eval e |> (eval1 |> s)) = refl
correct (if e e1 e2) s with correct e s
... | c with (exec (compile e) s) | (eval e)
correct (if e e1 e2) s | refl | .(True |> s) | True = correct e1 s
correct (if e e1 e2) s | refl | .(False |> s) | False = correct e2 s -}



{-
data Stack : forall {n : nat} -> List TyExp n -> Set where
  empty : Stack []
  _|>_ : {n : nat} -> {t : TyExp} -> {s : List TyExp n} -> (v : Val t) -> (xs : Stack s) -> Stack (t :: s)

top : {n : nat} -> {t : TyExp} -> {s : List TyExp n} -> Stack (t :: s) -> Val t
to p (v |> x) = v -}



{-
data Val : Set -> Set where
  nat : ℕ -> Val ℕ
  bool : Bool -> Val Bool

data Exp : ℕ -> Set -> Set₁ where
  val  : forall {t₁} -> (v : Val t₁) -> Exp zero t₁
  plus : (e₁ : Exp zero ℕ) -> (e₂ : Exp zero ℕ) -> Exp zero ℕ
  if   : forall {t} -> (b : Exp zero Bool) -> (e₁ e₂ : Exp zero t) -> Exp zero t
  var  : forall {n} -> Fin n -> Exp zero Bool
  let₁ : forall {t} -> Exp zero Bool -> Exp zero t -> Exp zero t



addv : Val ℕ -> Val ℕ -> Val ℕ
addv v₁ v₂ = {!!}

eval : forall { t₁ n n2 } -> (e : Exp n t₁) -> Vec (Val Bool) n2 -> Val t₁
eval (val v) env = v
eval (plus e₁ e₂) env with (eval e₁ env) | (eval e₂ env)
... | r1 | r2 = {!!}

eval (if e e₁ e₂) env with (eval e env) 
... | r = {!!}
eval (var x) env = {!!}
eval (let₁ e e₁) env = {!!}

-}

{-
eval (val v) _ = v
eval (plus e e1 ) env = (eval e env) + (eval e1 env)
eval (if p t e ) env = cond (eval p env) (eval t env) (eval e env)
eval (var i) env = {!!} -- lookup i env
eval (letx e₁ e₂) env = eval e₂ ((eval e₁ env) ∷ env) -}




{-

data Exp : nat -> TyExp -> Set where
  val  : forall { ty } -> (v : Val ty) -> Exp zero ty
  plus : (e1 : Exp zero TyNat) -> (e2 : Exp zero TyNat) -> Exp zero TyNat
  if   : forall { ty } -> (b : Exp zero Bool) -> (e1 e2 : Exp zero ty) -> Exp zero ty
  var  : forall { n} -> Fin n -> Exp zero Bool
  letx : forall { tz } -> Exp zero Bool -> Exp zero tz -> Exp zero tz


cond : forall {ty} -> Val Bool -> (t e : Val ty) -> Val ty
cond True t e = t
cond False t e = e
-}

{-
eval : forall { ty n n2 } -> (e : Exp n ty) -> Vec (Val Bool) n2 -> Val ty
eval (val v) _ = v
eval (plus e e1 ) env = (eval e env) + (eval e1 env)
eval (if p t e ) env = cond (eval p env) (eval t env) (eval e env)
eval (var i) env = {!!} -- lookup i env
eval (letx e₁ e₂) env = eval e₂ ((eval e₁ env) ∷ env)
-}

-- Prelude
{-
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
  TyNat  : TyExp
  Bool : TyExp

data Val : TyExp -> Set where
  True  : Val Bool
  False : Val Bool
  Zero : Val TyNat
  Succ : Val TyNat -> Val TyNat

data List (A : Set) : nat -> Set where
   [] : List A zero
   _::_ : {n : nat} -> A -> List A n -> List A (succ n)

-- N -> Set
  -- Var : Fin n -> Expr n
  -- Let : Expr n -> Expr (Succ n) -> Expr n

-- eval functie
--  eval : Expr t ctx -> Env ctx -> Val t

-- compilatie
-- LDS / STS (of POP) toevoegen
-- let e body
  -- compile e ++ compile body
  -- sts -1 om let variabelen weg te halen
-- var i = lds -i

data Fin : nat -> Set where
  Fz : forall {n} -> Fin (succ n)
  Fs : forall {n} -> Fin n -> Fin (succ n)

-- extensie : types van variables weghalen
-- kijken naar opgave lambda calculus

data Exp : nat -> TyExp -> Set where
  val  : forall { ty } -> (v : Val ty) -> Exp zero ty
  plus : (e1 : Exp zero TyNat) -> (e2 : Exp zero TyNat) -> Exp zero TyNat
  if   : forall { ty } -> (b : Exp zero Bool) -> (e1 e2 : Exp zero ty) -> Exp zero ty
  var  : forall { n} -> Fin n -> Exp zero Bool
  letx : forall { tz } -> Exp zero Bool -> Exp zero tz -> Exp zero tz


-- Basic functions

_+_ : (v1 v2 : Val TyNat) -> Val TyNat
Zero + m = m
Succ k + m = Succ (k + m)

cond : forall {ty } -> Val Bool -> (t e : Val ty) -> Val ty
cond True t e = t
cond False t e = e

-- Eval

eval : forall { ty n n2 } -> (e : Exp n ty) -> Vec (Val Bool) n2 -> Val ty
eval (val v) _ = v
eval (plus e e1 ) env = (eval e env) + (eval e1 env)
eval (if p t e ) env = cond (eval p env) (eval t env) (eval e env)
eval (var i) env = {!!} -- lookup i env
eval (letx e₁ e₂) env = eval e₂ ((eval e₁ env) ∷ env)

-- Stack

data Stack : forall {n : nat} -> List TyExp n -> Set where
  empty : Stack []
  _|>_ : {n : nat} -> {t : TyExp} -> {s : List TyExp n} -> (v : Val t) -> (xs : Stack s) -> Stack (t :: s)

top : {n : nat} -> {t : TyExp} -> {s : List TyExp n} -> Stack (t :: s) -> Val t
top (v |> x) = v


-- Code

data Code : {n k : nat} -> List TyExp n -> List TyExp k -> Set where
  skip : {n k : nat} -> {S : List TyExp n} -> {S' : List TyExp k} -> Code S S
  _++₁_ : {k l m : nat} -> {S0 : List TyExp k} -> {S1 : List TyExp l} -> {S2 : List TyExp m} -> Code S0 S1 -> Code S1 S2 -> Code S0 S2
  PUSH : {T : TyExp} -> {n : nat} -> {S : List TyExp n} -> Val T -> Code S (T :: S)
  ADD  : {n : nat} -> {S : List TyExp n} -> Code (Nat :: (Nat :: S)) (Nat :: S)
  IF   : {n k : nat} -> {S : List TyExp n} -> {S' : List TyExp k} -> Code S S' -> Code S S' -> Code (Bool :: S) S'  --not sure here either
  LDS  : {n : nat} {S : List TyExp n} {t : TyExp} -> Code S (t :: S)
  POP  : {n : nat} {S : List TyExp n} {t : TyExp} -> Code (t :: S) S

  -- LDS forall Ref S t -> Instr S (t :: S)
  -- POP i.p.v STS

exec : {n k : nat} ->{S : List TyExp n} -> {S' : List TyExp k} -> Code S S' -> Stack S -> Stack S'
exec skip s = s
exec (c ++₁ c₁) s = exec c₁ (exec c s)
exec (PUSH x) s = x |> s
exec ADD (v |> (v₁ |> s)) = (v + v₁) |> s
exec (IF c1 c2) (True |> s) = exec c1 s
exec (IF c1 c2) (False |> s) = exec c2 s
exec LDS x = {!!}
exec POP x = {!!}

compile : {n n2 : nat} -> {S : List TyExp n} -> {T : TyExp } -> Exp n2 T -> Code S ( T :: S)
compile (val v) = PUSH v
compile (plus e e₁) = compile e₁ ++₁ (compile e ++₁ ADD)
compile (if e e₁ e₂) = compile e ++₁ IF (compile e₁) (compile e₂)
compile (var i) = PUSH True
compile (letx e₁ e₂) = {!!}

-}

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
-}
