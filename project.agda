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
  _|>_ : forall {b t s} -> (v : Val t) -> (xs : Stack s) -> Stack (< b , t > ∷ s)

data Ref : Γ -> TyExp -> Set where
 Top : forall {G u} -> Ref (u ∷ G) (snd u)
 Pop : forall {G u v} -> Ref G u -> Ref (v ∷ G) u

data Exp : ℕ -> TyExp -> Γ -> Bool -> Set where
  val  : forall {t₁ ctx b} -> (v : Val t₁) -> Exp zero t₁ ctx b
  plus : forall {n ctx b} -> (e₁ : Exp n TyNat ctx false) -> (e₂ : Exp n TyNat ctx false) -> Exp n TyNat ctx b
  if   : forall {n t ctx b} -> (c : Exp n TyBool ctx false) -> (e₁ e₂ : Exp n t ctx b) -> Exp n t ctx b
  var  : forall {n ctx t b} -> Ref ctx t -> Exp n t ctx b
  let₁ : forall {n t₁ t₂ ctx b} -> Exp n t₁ ctx true -> Exp (suc n) t₂ (< true , t₁ >  ∷ ctx) b -> Exp n t₂ ctx b

slookup : forall {S t} -> Stack S -> Ref S t -> Val t
slookup (v |> xs) Top = v
slookup (v |> xs) (Pop b₁) = slookup xs b₁

cond : forall {ty} -> Val TyBool -> (t e : Val ty) -> Val ty
cond (bool true) b c = b
cond (bool false) b c = c

plus₁ : Val TyNat -> Val TyNat -> Val TyNat
plus₁ (nat x) (nat x₁) = nat (x + x₁)

eval : forall {t₁ n ctx b} -> (e : Exp n t₁ ctx b) -> Stack ctx -> Val t₁
eval (var x) env = slookup env x
eval (let₁ e₁ e₂) env = eval e₂ ((eval e₁ env) |> env)
eval (val v) env = v
eval (plus e₁ e₂) env = plus₁ (eval e₁ env) (eval e₂ env)
eval (if e e₁ e₂) env = cond (eval e env) (eval e₁ env) (eval e₂ env) 

data Code : Γ -> Γ -> Set where
    PUSH  : forall {S t b} -> Val t -> Code S (< b , t > ∷ S)
    LDS   : forall {S t b} -> (f : Ref S t) -> Code S (< b , t > ∷ S)
    POP   : forall {b S t₁ t₂} -> Code (< b , t₁ > ∷ (< true , t₂ > ∷ S)) (< b , t₁ > ∷ S)
    ADD   : forall {b S} -> Code (< false , TyNat > ∷ (< false , TyNat > ∷ S)) (< b , TyNat > ∷ S)
    IF    : forall {S S'} -> Code S S' -> Code S S' -> Code (< false , TyBool > ∷ S) S'
    skip  : {S S' : Γ} -> Code S S
    _++₁_ : forall {S S' S''} -> Code S S' -> Code S' S'' -> Code S S''

exec : {S S' : Γ} -> Code S S' -> Stack S -> Stack S'
exec (PUSH x) s = x |> s
exec (LDS f) s = (slookup s f) |> s
exec POP (v |> (v₁ |> s)) = v |> s
exec ADD (nat x |> (nat x₁ |> s)) = (nat (x₁ + x)) |> s
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

compile : forall {b S t n} -> (e : Exp n t (trimEnv S) b) -> Code S (< b , t > ∷ S)
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
lemma {[]} () s
lemma {< true , t > ∷ S} Top (v |> s) = refl
lemma {< true , x₁ > ∷ S} (Pop e) (v |> s) = lemma e s
lemma {< false , x₁ > ∷ S} e (v |> s) = lemma e s

correct : forall {b S t n} -> (e : Exp n t (trimEnv S) b) -> (s : Stack S) -> ((eval e (trimStack s)) |> s) ≡ (exec (compile e) s)
correct (val v) s = refl
correct (plus e e₁) s with correct e s
... | p1 with eval e (trimStack s) | exec (compile e) s
correct (plus e e₁) s | refl | p3 | .(p3 |> s) with correct e₁ (_|>_ {false} p3 s)
... | p2 with eval e₁ (trimStack s) | exec (compile e₁) (_|>_ {false} p3 s) 
correct (plus e e₁) s | refl | nat x | .(nat x |> s) | refl | nat x₁ | .(nat x₁ |> (nat x |> s)) = refl 
correct (if e e₁ e₂) s with correct e s
... | p1 with exec (compile e) s | eval e (trimStack s)
correct (if e e₁ e₂) s | refl | .(bool true |> s) | bool true = correct e₁ s
correct (if e e₁ e₂) s | refl | .(bool false |> s) | bool false = correct e₂ s
correct (var x) s with lemma x s
... | p with slookup (trimStack s) x | slookup s (convertRef x) 
correct (var x) s | refl | .l | l = refl
correct (let₁ e e₁) s with correct e s
... | p1 with exec (compile e) s | eval e (trimStack s)
correct (let₁ e e₁) s | refl | .(p3 |> s) | p3 with correct e₁ (_|>_ {true} p3 s)
... | p4 with exec (compile e₁) (_|>_ {true} p3 s) | eval e₁ (p3 |> trimStack s)
correct (let₁ e e₁) s | refl | .(p3 |> s) | p3 | refl | .(p6 |> (p3 |> s)) | p6 = refl
