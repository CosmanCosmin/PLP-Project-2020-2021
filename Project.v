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
| amodulus : AExp -> AExp -> AExp
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
Notation "A %' B" := (amodulus A B) (at level 48).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
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
Notation "A ||' B" := (bnot A B) (at level 52).

Inductive CExp :=
| cstring : stringType -> CExp
| cplus : CExp -> CExp -> CExp
| ctimes : AExp -> CExp -> CExp
| cfind : CExp -> CExp -> CExp
| ccompare : CExp -> CExp -> CExp
| cset : CExp -> CExp -> CExp
| crev : CExp -> CExp -> CExp
| clwr : CExp -> CExp
| cupr : CExp -> CExp.

Coercion cstring : stringType >-> CExp.
Inductive Array := 
| errorArray : Array
| natArray : nat -> list natType -> Array
| boolArray : nat -> list boolType -> Array
| stringArray : nat -> list stringType -> Array
| multiD : nat -> list Array -> Array.

Definition Params := list string.
Inductive State :=
| declareNat : string -> State
| assignNat : string -> AExp -> State
| declareBool : string -> State
| assignBool : string -> BExp -> State
| declareString : string -> State
| assignString : string -> CExp -> State
| declareArray : string -> Array ->State
| callFunction : string -> Params -> State
| sequence : State -> State -> State
| while : BExp -> State -> State
| ifthen : BExp -> State -> State
| ifelse : BExp -> State -> State -> State
| switch: AExp -> list cases -> State
with cases := 
| default : State -> cases
| case : nat -> State -> cases.

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
Notation "'Bool' A" := (declareBool A) (at level 98).
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
Check Bool "flag" ;; Switch (2 +' 2) : { Case (4): {"flag" :b:= btrue} ; Default : {"flag" :b:= bfalse}}.
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

Definition multiplyNatType (a b : natType) : natType :=
  match a, b with
  | num a, num b => num (a * b)
  | _, _ => errorNat
  end.
Compute multiplyNatType 2 2.
Compute multiplyNatType (plusNatType 1 1) (minusNatType 1 1). 

Definition divideNatType (a b : natType) : natType :=
  match a, b with
  | _, num 0 => errorNat
  | num a, num b => num (Nat.div a b)
  | _, _ => errorNat
  end.
Compute divideNatType 2 0.
Compute divideNatType 4 (multiplyNatType (plusNatType 0 1) (minusNatType 5 2)).

Definition moduloNatType (a b : natType) : natType :=
  match a, b with
  | _, num 0 => errorNat
  | num a, num b => num (Nat.modulo a b)
  | _, _ => errorNat
  end.
Compute moduloNatType 76 7.
Compute moduloNatType 0 0.

Definition lessBoolType (a b : natType) : boolType :=
  match a, b with
  | num a, num b => Boolean (Nat.ltb a b)
  | _, _ => errorBool
  end.
Compute lessBoolType 2 2. 
Compute lessBoolType (plusNatType 1 2) (multiplyNatType 2 2).

Definition greatBoolType (a b : natType) : boolType :=
  match a, b with
  | num a, num b => Boolean (Nat.ltb b a)
  | _, _ => errorBool
  end.
Compute greatBoolType 2 2. 
Compute greatBoolType (plusNatType 1 2) (multiplyNatType 2 2).

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
Fixpoint multiplyStringType (a : nat) (b c : Val) : stringType :=
  match a, b, c with
    | 0, strings b, _ => ""
    | 1, strings b, _ => b
    | S (a'), strings b, strings c =>  multiplyStringType a' (strings (append b c)) (strings c)
    | S (a'), strings b, _ => multiplyStringType a' (strings (append b b)) (strings b)
    | _, _, _ => errorString
  end.
Compute multiplyStringType 2 (strings "hei ") 0.
Compute multiplyStringType 3 (strings "uh ") 0.
Compute multiplyStringType 10 (strings "woo") 0.

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
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  