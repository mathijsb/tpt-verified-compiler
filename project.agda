module project where

open import Data.Bool
open import Data.List
open import Data.Vec
open import Data.Nat
open import Data.Fin hiding (_+_; _≤_)
open import Reflection
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _×_ (A B : Set) : Set where
  <_,_> : A -> B -> A × B

fst : {A B : Set} -> A × B -> A
fst < x , y > = x

snd : {A B : Set} -> A × B -> B
snd < x , y > = y

data TyExp : Set where
  TyNat  : TyExp
  TyBool : TyExp

data Val : TyExp -> Set where
  nat : ℕ -> Val TyNat
  bool : Bool -> Val TyBool

Γ : Set
Γ = List (Bool × TyExp)

data Stack : Γ -> Set where
  empty : Stack []
  _|>_ : forall {t s b} -> (v : Val t) -> (xs : Stack s) -> Stack (< b , t > ∷ s)

data Ref : Γ -> TyExp -> Set where
 Top : forall {G u} -> Ref (u ∷ G) (snd u)
 Pop : forall {G u v} -> Ref G u -> Ref (v ∷ G) u

data Exp : ℕ -> TyExp -> Γ -> Set where
  val  : forall {t₁ ctx} -> (v : Val t₁) -> Exp zero t₁ ctx
  plus : forall {n ctx} -> (e₁ : Exp n TyNat ctx) -> (e₂ : Exp n TyNat ctx) -> Exp n TyNat ctx
  if   : forall {n t ctx} -> (b : Exp n TyBool ctx) -> (e₁ e₂ : Exp n t ctx) -> Exp n t ctx
  var  : forall {n ctx t} -> Ref ctx t -> Exp n t ctx
  let₁ : forall {n t₁ t₂ ctx} -> Exp n t₁ ctx -> Exp (suc n) t₂ (< true , t₁ >  ∷ ctx) -> Exp n t₂ ctx

slookup : forall {S t} -> Stack S -> Ref S t -> Val t
slookup (v |> xs) Top = v
slookup (v |> xs) (Pop b₁) = slookup xs b₁

eval : forall {t₁ n ctx} -> (e : Exp n t₁ ctx) -> Stack ctx -> Val t₁
eval (var x) env = slookup env x
eval (let₁ e₁ e₂) env = eval e₂ ((eval e₁ env) |> env)
eval (val v) env = v
eval (plus e₁ e₂) env with (eval e₁ env) | (eval e₂ env)
eval (plus e₁ e₂) env | nat x₁ | nat x₂ = nat (x₁ + x₂)
eval (if e e₁ e₂) env with (eval e env) 
eval (if e e₁ e₂) env | bool true = eval e₁ env
eval (if e e₁ e₂) env | bool false = eval e₂ env

data Code : Γ -> Γ -> Set where
    PUSH  : forall {S t b} -> Val t -> Code S (< b , t > ∷ S)
    LDS   : forall {S t b} -> (f : Ref S t) -> Code S (< b , t > ∷ S)
    POP   : forall {S t₁ t₂ b} -> Code (< b , t₁ > ∷ (< true , t₂ > ∷ S)) (< b , t₁ > ∷ S)
    ADD   : forall {S b} -> Code (< false , TyNat > ∷ (< false , TyNat > ∷ S)) (< b , TyNat > ∷ S)
    IF    : forall {S S'} -> Code S S' -> Code S S' -> Code (< false , TyBool > ∷ S) S'
    skip  : {S S' : Γ} -> Code S S
    _++₁_ : forall {S S' S''} -> Code S S' -> Code S' S'' -> Code S S''

exec : {S S' : Γ} -> Code S S' -> Stack S -> Stack S'
exec (PUSH x) s = x |> s
exec (LDS f) s = (slookup s f) |> s
exec POP (v |> (v₁ |> s)) = v |> s
exec ADD (nat x |> (nat x₁ |> s)) = (nat (x + x₁)) |> s
exec (IF c₁ c₂) (bool true |> s) = exec c₁ s
exec (IF c₁ c₂) (bool false |> s) = exec c₂ s
exec skip s = s
exec (c ++₁ c₁) s = exec c₁ (exec c s)

trimEnv : Γ -> Γ
trimEnv [] = []
trimEnv (< true , x₁ > ∷ s) = < true , x₁ > ∷ trimEnv s
trimEnv (< false , x₁ > ∷ s) = trimEnv s

convertRef : forall {S t} -> Ref (trimEnv S) t -> Ref S t
convertRef {[]} ()
convertRef {< true , x₁ > ∷ S} Top = Top
convertRef {< true , x₁ > ∷ S} (Pop s) = Pop (convertRef s)
convertRef {< false , x₁ > ∷ S} s = Pop (convertRef s)

compile : forall {S t n b} -> (e : Exp n t (trimEnv S)) -> Code S (< b , t > ∷ S)
compile (val v) = PUSH v
compile (plus e e₁) = compile e ++₁ (compile e₁ ++₁ ADD)
compile (if e e₁ e₂) = compile e ++₁ IF (compile e₁) (compile e₂)
compile (var x) = LDS (convertRef x)
compile (let₁ e e₁) = compile e ++₁ (compile e₁ ++₁ POP)

trimStack : forall {S} -> Stack S -> Stack (trimEnv S)
trimStack {[]} x = empty
trimStack {< true , x₁ > ∷ S} (v |> x₂) = v |> (trimStack x₂)
trimStack {< false , x₁ > ∷ S} (v |> x₂) = trimStack x₂

lemma : forall {S t} -> (x : Ref (trimEnv S) t) -> (s : Stack S) -> (slookup (trimStack s) x) ≡ (slookup s (convertRef x))
lemma () empty
lemma e (v |> s₁) = {!!}

correct : forall {S t n b} -> (e : Exp n t (trimEnv S)) -> (s : Stack S) -> ((eval e (trimStack s)) |> s) ≡ (exec (compile {_} {_} {_} {b} e) s)
correct (val v) s = refl
correct (plus e e₁) s = {!!}
correct (if e e₁ e₂) s = {!!}
correct (var x) s with lemma x s
... | k = {!!}
correct (let₁ e e₁) s = {!!}

{-

Goal: append
      (eval (plus e e₁) (trimStack s) | eval e (trimStack s)
       | eval e₁ (trimStack s))
      false s
      ≡
      exec (ADD false)
      (exec (compile e₁ false) (exec (compile e false) s))

Goal: append (lookup₁ (stackToEnv s) x) false s ≡
      append (lookup₂ s (convertRef x)) false s

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
