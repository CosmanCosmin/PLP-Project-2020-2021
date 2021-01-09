(*Chestii triviale: variabile, if, for, while, alte chestii facute la lab/curs
Netriviale: strings, arrays, functions iterative/recursive, structs (maybe classes 
+ methods), switch - case, ternary operator, variable types?*)

Require Import Strings.String.
Open Scope string_scope.
Require Import List.
Local Open Scope list_scope.
Import ListNotations.
Require Import Bool.
Scheme Equality for string.

Inductive natType :=
| errorNat : natType
| num : nat -> natType.
Inductive boolType :=
| errorBool : boolType
| Boolean : bool -> boolType.
Inductive stringType :=
| errorString : stringType
| myString : string -> stringType.

Coercion num : nat >-> natType.
Coercion Boolean : bool >-> boolType.
Coercion myString : string >-> stringType.


Inductive AExp :=
| anat : natType -> AExp
| avar : string -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| atimes : AExp -> AExp -> AExp
| adivide : AExp -> AExp -> AExp
| amodulo : AExp -> AExp -> AExp
| alength : string -> AExp.

Coercion anat : natType >-> AExp.
Coercion avar : string >-> AExp.
Notation "A +' B" := (aplus A B) (at level 50).
Notation "A ++'" := (aplus A 1) (at level 50).
Notation "A -' B" := (aminus A B) (at level 50).
Notation "A --'" := (aminus A 1) (at level 50).
Notation "A *' B" := (atimes A B) (at level 48).
Notation "A **'" := (atimes A A) (at level 48).
Notation "A /' B" := (adivide A B) (at level 48).
Notation "A %' B" := (amodulo A B) (at level 48).
Notation "'LENGTH' A" := (alength A) (at level 50).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bvar : string -> BExp
| bless : AExp -> AExp -> BExp
| bgreat: AExp -> AExp -> BExp
| bequ : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.
Notation "A <' B" := (bless A B) (at level 52).
Notation "A >' B" := (bgreat A B) (at level 52).
Notation "A ==' B" :=  (bequ A B) (at level 52).
Notation "!' A" := (bnot A) (at level 52).
Notation "A >=' B" := (bnot (bless A B)) (at level 52).
Notation "A <=' B" := (bnot (bgreat A B)) (at level 52).
Notation "A &&' B" := (band A B) (at level 52).
Notation "A ||' B" := (bor A B) (at level 52).

Inductive CExp :=
| cvar : string -> CExp
| cstring : stringType -> CExp
| cplus : CExp -> CExp -> CExp
| ctimes : AExp -> CExp -> CExp
| csubstring : CExp -> CExp -> CExp
| ccompare : CExp -> CExp -> CExp
| cset : CExp -> CExp -> CExp
| crev : CExp -> CExp -> CExp.

Coercion cstring : stringType >-> CExp.

Definition Params := list string.
Inductive State :=
| declareNat : string -> State
| assignNat : string -> AExp -> State
| declareBool : string -> State
| assignBool : string -> BExp -> State
| declareString : string -> State
| assignString : string -> CExp -> State
| callFunction : string -> Params -> State
| sequence : State -> State -> State
| while : BExp -> State -> State
| ifthen : BExp -> State -> State
| ifelse : BExp -> State -> State -> State
| switch: AExp -> list cases -> State
with cases := 
| default : State -> cases
| case : natType -> State -> cases.

Inductive Val :=
| undecl: Val
| unassign: Val
| def: Val
| naturals : natType -> Val
| booleans : boolType -> Val
| strings : string -> Val.

Coercion naturals: natType >-> Val.
Coercion booleans: boolType >-> Val.
Scheme Equality for Val.
Compute booleans true.
Compute strings "test".

Inductive Struct :=
| declStruct : string -> list Val -> Struct.

Inductive Language :=
| declFunction : string -> Params -> State -> Language
| declGlobal: string -> Language
| declLocal : string -> Language
| declMain : State -> Language
| sequencer : Language -> Language -> Language.

Notation "'NAT' A" := (declareNat A) (at level 98).
Notation "'BOOL' A" := (declareBool A) (at level 98).
Notation "'STRING' A" := (declareString A) (at level 98).
Notation "A :n:= B" := (assignNat A B) (at level 98).
Notation "A :b:= B" := (assignBool A B) (at level 98).
Notation "A :s:= B" := (assignString A B) (at level 98).
Notation "A ;; B" := (sequence A B) (at level 98).
Notation "'If' '(' A ')' { B } 'else' { C }" := (ifelse A B C) (at level 96).
Notation "'If' '(' A ')' { B }" := (ifthen A B) (at level 96).
Notation "'While' '(' A ')' '{' B '}'" := (while A B) (at level 96).
Notation "'For' '(' A ';' B ';' C ')' '{' D '}'" := (A ;; while B (D ;; C)) (at level 96).
Notation "'Do' '{' A '}' 'While' '(' B ')'" := (A ;; while B A) (at level 96).
Notation "'Default' : { A }" := (default A) (at level 96).
Notation "'Case' ( A ) : { B }" := (case A B) (at level 96).
Notation "'Switch' ( A ) : { B } " := (switch A (cons B nil)) (at level 96).
Notation "'Switch' ( A ) : { B1 ; B2 ; .. ; Bn }" := (switch A (cons B1 (cons B2 .. (cons Bn nil) ..))) (at level 96).
Notation "'Function' A '(' B ')' '{' C '}'" := (declFunction A B C) (at level 96).
Notation "'Struct' A { B1 ';;' B2 ';;' .. ';;' Bn ';;' }" := (declStruct A (cons B1(cons B2 .. (cons Bn nil) ..))) (at level 96).
Notation "'main()' '{' A '}'" := (declMain A) (at level 99).
Notation "'global' A " := (declGlobal A) (at level 96).
Notation "A ;;; B " := (sequencer A B) (at level 96).

Check declareNat "test".
Check declFunction "a"  ["b"] (declareNat "c").
Check STRING "name".
Check STRING "name" ;; ("test" :s:= "no").
Check If ( 2 >=' 3 ) {"a" :b:= btrue}.
Check While ( "a" <' 4 ) { "a" :n:= "a" ++'}.
Check BOOL   "flag" ;; Switch (2 +' 2) : { Case (4): {"flag" :b:= btrue} ; Default : {"flag" :b:= bfalse}}.
Check For (NAT "i";; ("i" :n:= 10);"i" >=' 0;"i" :n:= "i"++') {"a" :n:= "a" +' "i"}.

Definition Env := string -> Val.
Definition startEnv : Env := fun x => undecl.
Compute (startEnv "hei").
Definition checkTypeEquality (a : Val)(b : Val) : bool :=
  match a with
 | undecl => match b with
            | undecl => true
            | _ => false
            end
 | unassign => match b with
            | unassign => true
            | _ => false
            end
 | def => match b with
            | def => true
            | _ => false
            end
 | naturals x => match b with
            | naturals x=> true
            | _ => false
            end
 | booleans x => match b with
            | booleans x => true
            | _ => false
            end
 | strings x => match b with
            | strings x => true
            | _ => false
            end
 end.

Definition update (env : Env) (variable : string) (value : Val) : Env := 
fun x =>
  if (string_beq x variable) then
    if ( andb ( checkTypeEquality undecl (env x)) ( negb ( checkTypeEquality def value)))
      then undecl
    else if ( andb ( checkTypeEquality undecl ( env x)) ( checkTypeEquality def value))
      then def
    else if ( orb ( checkTypeEquality def (env x)) (checkTypeEquality value (env x)))
      then value
    else unassign
  else (env x).

Compute (startEnv "string").
Compute (update startEnv "x" (booleans false) "x").
Compute (update (update startEnv "x" def) "x" (naturals 25)) "x".

Definition plusNatType (a b : natType) : natType :=
  match a, b with
  | num a, num b => num (a + b)
  | _, _ => errorNat
  end.
Compute plusNatType 1 1.
Compute plusNatType (plusNatType 2 3) 2.

Definition minusNatType (a b : natType) : natType :=
  match a, b with
  | num a, num b => if Nat.ltb a b then errorNat
                    else num (a - b)
  | _, _ => errorNat
  end.
Compute minusNatType 2 (plusNatType 1 3).
Compute minusNatType (minusNatType 7 2) (plusNatType 1 2).

Definition timesNatType (a b : natType) : natType :=
  match a, b with
  | num a, num b => num (a * b)
  | _, _ => errorNat
  end.
Compute timesNatType 2 2.
Compute timesNatType (plusNatType 1 1) (minusNatType 1 1). 

Definition divideNatType (a b : natType) : natType :=
  match a, b with
    | _, num 0 => errorNat
    | num a, num b => num (Nat.div a b)
    | _, _ => errorNat
  end.
Compute divideNatType 2 0.
Compute divideNatType 4 (timesNatType (plusNatType 0 1) (minusNatType 5 2)).

Definition moduloNatType (a b : natType) : natType :=
  match a, b with
   | _, num 0 => errorNat
   | num a, num b => num (Nat.modulo a b)
   | _, _ => errorNat
  end.
Compute moduloNatType 76 7.
Compute moduloNatType 0 0.

Definition equalBoolType (a b : natType) : boolType :=
  match a, b with
    | num a, num b => Boolean (Nat.eqb a b)
    | _, _ => errorBool
  end.
Definition lessBoolType (a b : natType) : boolType :=
  match a, b with
    | num a, num b => Boolean (Nat.ltb a b)
    | _, _ => errorBool
  end.
Compute lessBoolType 2 2. 
Compute lessBoolType (plusNatType 1 2) (timesNatType 2 2).

Definition greatBoolType (a b : natType) : boolType :=
  match a, b with
    | num a, num b => Boolean (Nat.ltb b a)
    | _, _ => errorBool
  end.
Compute greatBoolType 2 2. 
Compute greatBoolType (plusNatType 1 2) (timesNatType 2 2).

Definition notBoolType (a : boolType) : boolType :=
  match a with
    | Boolean a => Boolean (negb a)
    | _ => errorBool
  end.
Compute notBoolType (greatBoolType 2 2).

Definition andBoolType (a b : boolType) : boolType :=
  match a, b with
    | Boolean a, Boolean b => Boolean (andb a b)
    | _, _ => errorBool
  end.
Compute andBoolType (notBoolType (greatBoolType 2 2)) (lessBoolType 5 6).

Definition orBoolType (a b : boolType) : boolType :=
  match a, b with
  | Boolean a, Boolean b => Boolean (orb a b)
  | _, _ => errorBool
  end.
Compute orBoolType true false.

Fixpoint append (a b : string) : string :=
  match a with
    | EmptyString => b
    | String c a' => String c (append a' b)
  end.
Definition appendStringType (a b : Val) : stringType :=
  match a, b with
    | strings a, strings b => append a b 
    | _, _ => errorString
  end.
Compute appendStringType (strings "no") (strings " coq").
Fixpoint multiply (a : nat) (b : string) : string :=
  match a, b with
    | 0, _ => ""
    | _, EmptyString => ""
    | 1, String c b' => b
    | S a', String c b' => append b (multiply a' b)
  end.
Compute multiply 3 "oof".
Definition multiplyStringType (a : nat) (b : Val) : stringType :=
  match a, b with
    | a, strings b => multiply a b 
    | _, _ => errorString
  end.
Compute multiplyStringType 2 (strings "hei ").
Compute multiplyStringType 3 (strings "uh ").

Definition compareStringType (a b : Val) : boolType :=
  match a, b with
    | strings a, strings b => string_beq a b
    | _, _ => errorBool
  end.
Compute compareStringType (strings "unu") (strings "doi").
Compute compareStringType (strings "a") (strings "a").

Fixpoint stringLength (s : string) : nat :=
  match s with
    | EmptyString => 0
    | String c s' => S (stringLength s')
  end.
Definition lengthStringType (string : Val) : natType :=
  match string with 
    | strings s => stringLength s
    | _ => errorNat
  end.

Fixpoint substring (n m : nat) (s : string) : string :=
  match n, m, s with
    | 0, 0, _ => EmptyString
    | 0, S m', EmptyString => s
    | 0, S m', String c s' => String c (substring 0 m' s')
    | S n', _, EmptyString => s
    | S n', _, String c s' => substring n' m s'
  end.
Compute substring 0 1 "First Char".
Definition subStringType (n m : nat) (s : Val) : stringType :=
  match n, m, s with 
    | n, m, strings s => substring n m s
    | _, _, _ => errorString
  end.
Compute subStringType 0 3 (strings "Buenos dias").

Fixpoint reverseString (s : string) : string :=
  match s with
    | EmptyString => s
    | String c s' => append (reverseString s') (substring 0 1 s)
  end.
Compute reverseString "auiz anub".
Definition reverseStringType (s : Val) : stringType :=
  match s with 
    | strings s => reverseString s
    | _ => errorString
  end.
Compute reverseStringType (strings "erom on epon").

Fixpoint aEval (x : AExp) (env : Env) : natType :=
  match x with
    | anat x => x
    | avar variable => match (env variable) with
                         | naturals nr => nr
                         | _ => errorNat
                       end
    | aplus a b => (plusNatType (aEval a env) (aEval b env))
    | aminus a b => (minusNatType (aEval a env) (aEval b env))
    | atimes a b => (timesNatType (aEval a env) (aEval b env))
    | adivide a b => (divideNatType (aEval a env) (aEval b env))
    | amodulo a b => (moduloNatType (aEval a env) (aEval b env))
    | alength a => (lengthStringType (env a))
  end.
Compute aEval ("var1" *' "var1") (update (update startEnv "var1" def) "var1" 12).

Fixpoint bEval (x : BExp) (env : Env) : boolType :=
  match x with
    | btrue => true
    | bfalse => false
    | bvar variable => match (env variable) with
                  | booleans v => v
                  | _ => errorBool
                end
    | bless a b => (lessBoolType (aEval a env) (aEval b env))
    | bgreat a b => (greatBoolType (aEval a env) (aEval b env))
    | bequ a b => (equalBoolType (aEval a env) (aEval b env))
    | bnot a => (notBoolType (bEval a env))
    | band a b => (andBoolType (bEval a env) (bEval b env))
    | bor a b => (orBoolType (bEval a env) (bEval b env))
  end.
Compute bEval (((2 +' 2) <' 3) ||' ("unu" >' "zero")) (update (update (update (update startEnv "zero" def) "zero" 0) "unu" def) "unu" 1).

Definition declarations (x : State) : nat :=
  match x with
    | declareNat x => 1
    | declareBool x => 2
    | declareString x => 3
    | _ => 0
  end.
Definition defaultValues (n : nat) : Val :=
  match n with
    | 1 => naturals 1
    | 2 => booleans false
    | 3 => strings ""
    | _ => def
  end.

Inductive List :=
| nil : List
| push : nat -> List -> List.
Fixpoint lengthList (list : List) : nat :=
  match list with
    | nil => 0
    | push _ list' => S (lengthList list')
  end.
Compute lengthList (push 2 (push 3 (push 4(push 5 nil)))).
Fixpoint nthElement (n : nat) (list : List) : nat :=
  match n, list with
    | _, nil => 0
    | _, push x nil => x
    | 0, push x list' => x
    | S n', push x list' => nthElement n' list'
  end. 
Compute nthElement 6 (push 2 (push 3 (push 4(push 5 nil)))).

Inductive Array := 
| errorArray : Array
| natArray : string -> nat -> List -> Array.
Compute natArray "test" 5 (nil).
Notation "'emptyArray' A ';' B ';' " := (natArray A B nil) (at level 70).
Notation "'array' A ';' B ';' '=' [ a , .. , b ] " := (natArray A B (push a .. (push b nil) ..))(at level 80).
Compute emptyArray "pls work" ;10; .
Compute array "yes" ;2; = [ 2 , 3 ].