
module project where

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

data Exp : TyExp -> Set where
  val  : forall { ty } -> (v : Val ty) -> Exp ty
  plus : (e1 : Exp Nat) -> (e2 : Exp Nat) -> Exp Nat
--  if   : forall { ty } -> (b : Exp Bool) -> (e1 e2 : Exp ty) -> Exp ty


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
-- eval (if p t e ) = cond (eval p) (eval t) (eval e )


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

data Code : {n k : nat} -> List TyExp n -> List TyExp k -> Set where
  skip : {n k : nat} -> {S : List TyExp n} -> {S' : List TyExp k} -> Code S S
  _++_ : {k l m : nat} -> {S0 : List TyExp k} -> {S1 : List TyExp l} -> {S2 : List TyExp m} -> Code S0 S1 -> Code S1 S2 -> Code S0 S2
  PUSH : {T : TyExp} -> {n : nat} -> {S : List TyExp n} -> Val T -> Code S (T :: S)
  ADD  : {n : nat} -> {S : List TyExp n} -> Code (Nat :: (Nat :: S)) (Nat :: S)
--  IF   : {n k : nat} -> {S : List TyExp n} -> {S' : List TyExp k} -> Code S S' -> Code S S' -> Code (Bool :: S) S'  --not sure here either

exec : {n k : nat} ->{S : List TyExp n} -> {S' : List TyExp k} -> Code S S' -> Stack S -> Stack S'
exec skip s = s
exec (c ++ c₁) s = exec c₁ (exec c s)
exec (PUSH x) s = x |> s
exec ADD (v |> (v₁ |> s)) = (v + v₁) |> s
--exec (IF c1 c2) (True |> s) = exec c1 s
--exec (IF c1 c2) (False |> s) = exec c2 s

compile : {n : nat} -> {S : List TyExp n} -> {T : TyExp } -> Exp T -> Code S ( T :: S)
compile (val v) = PUSH v
compile (plus e e₁) = compile e₁ ++ (compile e ++ ADD)
--compile (if e e₁ e₂) = compile e ++ IF (compile e₁) (compile e₂)


-- Correct

-- lemma2 : ((c + v₂) |> a) ≡ (v |> d)

lemma : {n : nat} 
        -> {S : List TyExp n} 
        -> (e e₁ : Exp Nat)
        -> (s : Stack S)
        -> ((eval e) |> s) ≡ (exec (compile e) s) 
        -> ((eval e₁) |> s) ≡ (exec (compile e₁) s)
        -> ((eval e + eval e₁) |> s) ≡ exec ADD (exec (compile e) (exec (compile e₁) s))
lemma e1 e2 s p1 p2 with (exec (compile e2) s) | (exec (compile e1) s) | (eval e1) | (eval e2)
lemma e1 e2 .a refl refl | v |> a | .(c |> a) | c | .v with exec (compile e1) (c |> a)
lemma e1 e2 .a refl refl | v |> a | .(c |> a) | c | .v | v₁ |> b with exec ADD (eval e1 |> (eval e2 |> a))
lemma e1 e2 .a refl refl | v₁ |> a | .(c |> a) | c | .v₁ | v₂ |> b | v |> x = {!!}

--lemma e1 e2 .a refl refl | v₃ |> a | .(c |> a) | c | .v₃ | v₂ |> b | v₁ |> x | v |> q = {!!}



--lemma e1 e2 .a refl refl | v₂ |> a | .(c |> a) | c | .v₂ | v₁ |> b | v |> d = {!!}

--lemma e1 e2 s refl refl | .(r |> s) | .(q |> s) | q | r | s = {!!}

{- lemma e1 e2 s refl refl | .(eval e2 |> s) | .(eval e1 |> s) with (eval e1) | (eval e2)
... | o | p with (exec (compile e1) (p |> s))
lemma e1 e2 s refl refl | .(eval e2 |> s) | .(eval e1 |> s) | o | p | v |> (v₁ |> q) with exec ADD (exec (compile e1) (exec (compile e2) s))
lemma e1 e2 s refl refl | .(eval e2 |> s) | .(eval e1 |> s) | o | p | v₁ |> (v₂ |> q) | v |> r = {!!} -}


{-
lemma (val v) (val v₁) s p1 p2 = refl
lemma (val v) (plus e₁ e₂) s refl p2 with (exec ADD (exec (compile e₁) (exec (compile e₂) s)))
lemma (val v) (plus e₁ e₂) s refl refl | .((eval e₁ + eval e₂) |> s) = refl
lemma (val v) (if e2 e3 e4) s p1 p2 = {!!}
lemma (plus e1 e2) e3 s p1 p2 = {!!}
lemma (if e1 e2 e3) e4 s p1 p2 = {!!}-}

{-
lemma e1 e2 s p1 p2 with (exec (compile e2) s) | (exec (compile e1) s)
lemma e1 e2 s refl refl | .(eval e2 |> s) | .(eval e1 |> s) with (eval e1) | (eval e2)
... | o | p with (exec (compile e1) (p |> s))
lemma e1 e2 s refl refl | .(eval e2 |> s) | .(eval e1 |> s) | o | p | v |> (v₁ |> q) with exec ADD (exec (compile e1) (exec (compile e2) s))
lemma e1 e2 s refl refl | .(eval e2 |> s) | .(eval e1 |> s) | o | p | v₁ |> (v₂ |> q) | v |> r = {!!} -}


{-
lemma e1 e2 s p1 p2 with eval e1 | eval e2 | (exec (compile e2) s) | (exec (compile e1) s)
lemma e1 e2 s refl refl | l | m | .(m |> s) | .(l |> s) with exec (compile e1) (m |> s)
lemma e1 e2 s refl refl | l | m | .(m |> s) | .(l |> s) | v |> (v₁ |> q) with exec ADD (exec (compile e1) (exec (compile e2) s))
lemma e1 e2 s refl refl | l | m | .(m |> s) | .(l |> s) | v₁ |> (v₂ |> q) | v |> x = {!!}
-}

-- ... | o = ?

{-
lemma (val v) (val v₁) s refl refl = refl
lemma (val v) (plus e₁ e₂) s refl p2 with (exec ADD (exec (compile e₁) (exec (compile e₂) s)))
lemma (val v) (plus e₁ e₂) s refl refl | .((eval e₁ + eval e₂) |> s) = refl
--lemma (val v) (plus e₁ e₂) s refl p2 with eval e₁ | eval e₂ --  | exec ADD (v |> exec ADD (exec (compile e₁) (exec (compile e₂) s)))
--lemma (val v) (plus e₁ e₂) s refl p2 | k | l with (exec ADD (exec (compile e₁) (exec (compile e₂) s)))
--lemma (val v) (plus e₁ e₂) s refl refl | k | l | .((k + l) |> s) = refl
lemma (val v) (if e₁ e₂ e₃) s refl p2 = {!!}
lemma (plus e e₁) (val v) s p1 p2 = {!!}
lemma (plus e e₁) (plus e₂ e₃) s p1 p2 with exec ADD (exec (compile e₂) (exec (compile e₃) s)) | exec ADD (exec (compile e) (exec (compile e₁) s))
... | k | l with exec ADD (exec ADD (exec (compile e) (exec (compile e₁) k)))
... | m with eval e | eval e₁ | eval e₂ | eval e₃
lemma (plus e e₁) (plus e₂ e₃) s refl refl | .((q + r) |> s) | .((o + p) |> s) | m | o | p | q | r = {!!} 
lemma (plus e e₁) (if e₂ e₃ e₄) s p1 p2 = {!!}
lemma (if e e₁ e₂) (val v) s p1 refl = {!!}
lemma (if e e₁ e₂) (plus e₃ e₄) s p1 p2 = {!!}
lemma (if e e₁ e₂) (if e₃ e₄ e₅) s p1 p2 = {!!} -}

-- lemma2 :

--Goal: ((v + (eval e₁ + eval e₂)) |> s) ≡
--      exec ADD (v |> exec ADD (exec (compile e₁) (exec (compile e₂) s)))

correct : {T : TyExp} -> {n : nat} -> {S : List TyExp n} -> (e : Exp T) -> (s : Stack S) -> ((eval e) |> s) ≡ (exec (compile e) s)
correct (val v) s = refl
correct (plus e e₁) s with correct e s | correct e₁ s
correct (plus e e₁) s | k | l = lemma e e₁ s k l
--correct (if e e₁ e₂) s with correct e s
-- ... | k = {!!}
