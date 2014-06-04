
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
  append : {t : TyExp} -> {s : Γ} -> (v : Val t) -> (b : Bool) -> (xs : Stack s) -> Stack (< b , t > ∷ s)

data Ref : Γ -> TyExp -> Set where
 Top : forall {G u} -> Ref (u ∷ G) (snd u)
 Pop : forall {G u v} -> Ref G u -> Ref (v ∷ G) u

data Exp : ℕ -> TyExp -> Γ -> Set where
  val  : forall {t₁ ctx} -> (v : Val t₁) -> Exp zero t₁ ctx
  plus : forall {n ctx} -> (e₁ : Exp n TyNat ctx) -> (e₂ : Exp n TyNat ctx) -> Exp n TyNat ctx
  if   : forall {n t ctx} -> (b : Exp n TyBool ctx) -> (e₁ e₂ : Exp n t ctx) -> Exp n t ctx
  var  : forall {n ctx t} -> Ref ctx t -> Exp n t ctx
  let₁ : forall {n t₁ t₂ ctx} -> Exp n t₁ ctx -> Exp (suc n) t₂ (< true , t₁ >  ∷ ctx) -> Exp n t₂ ctx

slookup : {S : Γ} -> {t : TyExp} -> Stack S -> Ref S t -> Val t
slookup (append v b a) Top = v
slookup (append v b a) (Pop b₁) = slookup a b₁

eval : forall { t₁ n ctx} -> (e : Exp n t₁ ctx) -> Stack ctx -> Val t₁
eval (var x) env = slookup env x
eval (let₁ e₁ e₂) env = eval e₂ (append (eval e₁ env) true env)
eval (val v) env = v
eval (plus e₁ e₂) env with (eval e₁ env) | (eval e₂ env)
eval (plus e₁ e₂) env | nat x₁ | nat x₂ = nat (x₁ + x₂)
eval (if e e₁ e₂) env with (eval e env) 
eval (if e e₁ e₂) env | bool true = eval e₁ env
eval (if e e₁ e₂) env | bool false = eval e₂ env

data Code : Γ -> Γ -> Set where
    PUSH  : {t : TyExp} -> {S : Γ} -> (b : Bool) -> Val t -> Code S (< b , t > ∷ S)
    LDS   : {t : TyExp} -> {S : Γ} -> (b : Bool) -> (f : Ref S t) -> Code S (< b , t > ∷ S)
    POP   : {t₁ t₂ : TyExp} -> {S : Γ} -> {b₁ b₂ : Bool} -> Code (< b₁ , t₁ > ∷ (< b₂ , t₂ > ∷ S)) (< b₁ , t₁ > ∷ S)
    ADD   : {S : Γ} -> {b₁ b₂ : Bool} -> (b : Bool) -> Code (< b₁ , TyNat > ∷ (< b₂ , TyNat > ∷ S)) (< b , TyNat > ∷ S)
    IF    : {S S' : Γ} -> {b : Bool} -> Code S S' -> Code S S' -> Code (< b , TyBool > ∷ S) S'
    skip  : {S S' : Γ} -> Code S S
    _++₁_ : {S0 S1 S2 : Γ} -> Code S0 S1 -> Code S1 S2 -> Code S0 S2

exec : {S S' : Γ} -> Code S S' -> Stack S -> Stack S'
exec (PUSH b x) s = append x b s
exec (LDS b f) s = append (slookup s f) b s
exec (POP {t₁} {t₂} {S} {b₁} {b₂}) (append v .b₁ (append v₁ .b₂ s)) = append v b₁ s
exec (ADD {S} {b₁} {b₂} b) (append (nat x) .b₁ (append (nat x₁) .b₂ s)) = append (nat (x + x₁)) b s
exec (IF c c₁) (append (bool true) b s) = exec c s
exec (IF c c₁) (append (bool false) b s) = exec c₁ s
exec skip s = s
exec (c ++₁ c₁) s = exec c₁ (exec c s)

trimEnv : Γ -> Γ
trimEnv [] = []
trimEnv (< true , x₁ > ∷ s) = < true , x₁ > ∷ trimEnv s
trimEnv (< false , x₁ > ∷ s) = trimEnv s

convertRef : {S : Γ} -> {T : TyExp} -> Ref (trimEnv S) T -> Ref S T
convertRef {[]} ()
convertRef {< true , x₁ > ∷ S} Top = Top
convertRef {< true , x₁ > ∷ S} (Pop s) = Pop (convertRef s)
convertRef {< false , x₁ > ∷ S} s = Pop (convertRef s)

compile : {n : ℕ} -> {S : Γ} -> {T : TyExp} -> (e : Exp n T (trimEnv S)) -> (b : Bool) -> Code S (< b , T > ∷ S)
compile (val v) b = PUSH b v
compile (plus e e₁) true = compile e false ++₁ (compile e₁ false ++₁ (ADD true))
compile (plus e e₁) false = compile e false ++₁ (compile e₁ false ++₁ (ADD false))
compile (if e e₁ e₂) b = compile e b ++₁ IF (compile e₁ b) (compile e₂ b)
compile (var x) b = LDS b (convertRef x)
compile (let₁ e e₁) b = compile e true ++₁ (compile e₁ b ++₁ POP)

-- Correct
trimStack : {S : Γ} -> Stack S -> Stack (trimEnv S)
trimStack empty = empty
trimStack (append v true s₁) = append v true (trimStack s₁)
trimStack (append v false s₁) = trimStack s₁

lemma : {t : TyExp} -> {S : Γ} -> (x : Ref (trimEnv S) t) -> (s : Stack S) -> (slookup (trimStack s) x) ≡ (slookup s (convertRef x))
lemma () empty
lemma r (append v b s₁) = {!!}

correct : {T : TyExp} -> {n : ℕ} -> {S : Γ} -> (e : Exp n T (trimEnv S)) -> (s : Stack S) -> (append (eval e (trimStack s)) false s) ≡ (exec (compile e false) s)
correct {T} {zero} {S} (val v) s = refl
correct {TyNat} {n} {S} (plus e e₁) s with correct e s | correct e₁ s
... | k | l with (exec (compile e false) s)
... | m = {!!} 
correct {T} {n} {S} (if e e₁ e₂) s = {!!}
correct {T} {n} {S} (var x) s = {!!} 
correct {T} {n} {S} (let₁ e e₁) s = {!!}

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
