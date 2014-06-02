
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

Context : Set
Context = List TyExp

data Env : Context -> Set where
  empty : Env []
  _|+_ : {t : TyExp} -> {s : List TyExp} -> (v : Val t) -> Env s -> Env (t ∷ s)

data Ref : Context -> TyExp -> Set where
 Top : forall {G u} -> Ref (u ∷ G) u
 Pop : forall {G u v} -> Ref G u -> Ref (v ∷ G) u

data Exp : ℕ -> TyExp -> Context -> Set where
  val  : forall {t₁ ctx} -> (v : Val t₁) -> Exp zero t₁ ctx
  plus : forall {n ctx} -> (e₁ : Exp n TyNat ctx) -> (e₂ : Exp n TyNat ctx) -> Exp n TyNat ctx
  if   : forall {n t ctx} -> (b : Exp n TyBool ctx) -> (e₁ e₂ : Exp n t ctx) -> Exp n t ctx
  var  : forall {n ctx t} -> Ref ctx t -> Exp n t ctx
  let₁ : forall {n t₁ t₂ ctx} -> Exp n t₁ ctx -> Exp (suc n) t₂ (t₁ ∷ ctx) -> Exp n t₂ ctx

lookup₁ : {S : List TyExp} -> {t : TyExp} -> Env S -> Ref S t -> Val t
lookup₁ (v |+ e) Top = v
lookup₁ (v₁ |+ e) (Pop r) = lookup₁ e r

eval : forall { t₁ n ctx} -> (e : Exp n t₁ ctx) -> Env ctx -> Val t₁
eval (var x) env = lookup₁ env x
eval (let₁ e₁ e₂) env = eval e₂ ((eval e₁ env) |+ env)
eval (val v) env = v
eval (plus e₁ e₂) env with (eval e₁ env) | (eval e₂ env)
eval (plus e₁ e₂) env | nat x₁ | nat x₂ = nat (x₁ + x₂)
eval (if e e₁ e₂) env with (eval e env) 
eval (if e e₁ e₂) env | bool true = eval e₁ env
eval (if e e₁ e₂) env | bool false = eval e₂ env

StackContext : Set
StackContext = List (Bool × TyExp)

data Ref₂ : StackContext -> TyExp -> Set where
 Top : forall {G u} -> Ref₂ (u ∷ G) (snd u)
 Pop : forall {G u v} -> Ref₂ G u -> Ref₂ (v ∷ G) u

data Code : StackContext -> StackContext -> Set where
    PUSH  : {t : TyExp} -> {S : StackContext} -> (b : Bool) -> Val t -> Code S (< b , t > ∷ S)
    LDS   : {t : TyExp} -> {S : StackContext} -> (b : Bool) -> (f : Ref₂ S t) -> Code S (< b , t > ∷ S)
    POP   : {t₁ t₂ : TyExp} -> {S : StackContext} -> {b₁ b₂ : Bool} -> Code (< b₁ , t₁ > ∷ (< b₂ , t₂ > ∷ S)) (< b₁ , t₁ > ∷ S)
    ADD   : {S : StackContext} -> {b₁ b₂ : Bool} -> (b : Bool) -> Code (< b₁ , TyNat > ∷ (< b₂ , TyNat > ∷ S)) (< b , TyNat > ∷ S)
    IF    : {S S' : StackContext} -> {b : Bool} -> Code S S' -> Code S S' -> Code (< b , TyBool > ∷ S) S'
    skip  : {S S' : StackContext} -> Code S S
    _++₁_ : {S0 S1 S2 : StackContext} -> Code S0 S1 -> Code S1 S2 -> Code S0 S2

data Stack : StackContext -> Set where
  empty : Stack []
  append : {t : TyExp} -> {s : StackContext} -> (v : Val t) -> (b : Bool) -> (xs : Stack s) -> Stack (< b , t > ∷ s)

lookup₂ : {S : StackContext} -> {t : TyExp} -> Stack S -> Ref₂ S t -> Val t
lookup₂ (append v b s) Top = v
lookup₂ (append v b s) (Pop r) = lookup₂ s r

exec : {S S' : StackContext} -> Code S S' -> Stack S -> Stack S'
exec (PUSH b x) s = append x b s
exec (LDS b f) s = append (lookup₂ s f) b s
exec (POP {t₁} {t₂} {S} {b₁} {b₂}) (append v .b₁ (append v₁ .b₂ s)) = append v b₁ s
exec (ADD {S} {b₁} {b₂} b) (append (nat x) .b₁ (append (nat x₁) .b₂ s)) = append (nat (x + x₁)) b s
exec (IF c c₁) (append (bool true) b s) = exec c s
exec (IF c c₁) (append (bool false) b s) = exec c₁ s
exec skip s = s
exec (c ++₁ c₁) s = exec c₁ (exec c s)

stackContextToContext : StackContext -> Context
stackContextToContext [] = []
stackContextToContext (< true , x₁ > ∷ s) = x₁ ∷ stackContextToContext s
stackContextToContext (< false , x₁ > ∷ s) = stackContextToContext s

convertRef : {S : StackContext} -> {T : TyExp} -> Ref (stackContextToContext S) T -> Ref₂ S T
convertRef {[]} ()
convertRef {< true , x₁ > ∷ S} Top = Top
convertRef {< true , x₁ > ∷ S} (Pop s) = Pop (convertRef s)
convertRef {< false , x₁ > ∷ S} s = Pop (convertRef s)

compile : {n : ℕ} -> {S : StackContext} -> {T : TyExp} -> (e : Exp n T (stackContextToContext S)) -> (b : Bool) -> Code S (< b , T > ∷ S)
compile (val v) b = PUSH b v
compile (plus e e₁) true = compile e false ++₁ (compile e₁ false ++₁ (ADD true))
compile (plus e e₁) false = compile e false ++₁ (compile e₁ false ++₁ (ADD false))
compile (if e e₁ e₂) b = compile e b ++₁ IF (compile e₁ b) (compile e₂ b)
compile (var x) b = LDS b (convertRef x)
compile (let₁ e e₁) b = compile e true ++₁ (compile e₁ b ++₁ POP)

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
