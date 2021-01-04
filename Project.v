(*Chestii triviale: variabile, if, for, while, alte chestii facute la lab/curs
Netriviale: strings, arrays, functions iterative/recursive, structs (maybe classes 
+ methods), switch - case, ternary operator, variable types?*)

Require Import String.
Open Scope string_scope.
Require Import List.
Local Open Scope list_scope.
Import ListNotations.
Require Import Coq.ZArith.BinInt.
Local Open Scope Z_scope.
Require Import Bool.
Scheme Equality for string.

Inductive natType :=
| errorNat : natType
| num : nat -> natType.
Inductive intType :=
| errorInt : intType
| integ : Z -> intType.
Inductive boolType :=
| errorBool : boolType
| Boolean : bool -> boolType.
Inductive stringType :=
| errorString : stringType
| String : string -> stringType.

Coercion num : nat >-> natType.
Coercion integ : Z >-> intType.
Coercion String : string >-> stringType.
Definition Variables := string.

Inductive AExp :=
| anat : natType -> AExp
| aint : intType -> AExp
| avar : string -> AExp
| aplus : AExp -> AExp -> AExp
| aminus : AExp -> AExp -> AExp
| atimes : AExp -> AExp -> AExp
| adivide : AExp -> AExp -> AExp
| amodulus : AExp -> AExp -> AExp.

Coercion anat : natType >-> AExp.
Coercion aint : intType >-> AExp.
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
| clength : CExp -> CExp
| ccompare : CExp -> CExp -> CExp
| cset : CExp -> CExp -> CExp
| crev : CExp -> CExp -> CExp
| clwr : CExp -> CExp
| cupr : CExp -> CExp.

Coercion cstring : stringType >-> CExp.
Inductive Array := 
| errorArray : Array
| intArray : nat -> list intType -> Array
| natArray : nat -> list natType -> Array
| boolArray : nat -> list boolType -> Array
| stringArray : nat -> list stringType -> Array
| multiD : nat -> list Array -> Array.

Definition Params := list string.
Inductive State :=
| declareNat : string -> State
| assignNat : string -> AExp -> State
| declareInt : string -> State
| assignInt : string -> AExp -> State
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
| integers : intType -> Val
| booleans : boolType -> Val
| strings : stringType -> Val
| arrays : Array -> Val
| code: State -> Val.

Coercion naturals: natType >-> Val.
Coercion integers: intType >-> Val.
Coercion booleans: boolType >-> Val.
Coercion strings : stringType >-> Val.
Coercion code: State >-> Val.

Inductive Struct :=
| declStruct : string -> list Val -> Struct.

Inductive Language :=
| declFunction : string -> Params -> State -> Language
| declGlobal: Variables -> Language
| declLocal : Variables -> Language
| declMain : State -> Language
| sequencer : Language -> Language -> Language.

Notation "'nat' A" := (declareNat A) (at level 98).
Notation "'int' A" := (declareInt A) (at level 98).
Notation "'Bool' A" := (declareBool A) (at level 98).
Notation "'String' A" := (declareString A) (at level 98).
Notation "A :n:= B" := (assignNat A B) (at level 98).
Notation "A :i:= B" := (assignInt A B) (at level 98).
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
Notation "'int' A [ B ] { C1 ; C2 ; .. ; Cn }" := ( declareArray A ( intArray B (cons (integ C1) (cons (integ C2) .. (cons (integ Cn) nil) ..) ) ) )(at level 96).
Notation "'int' A [ B ]" := ( declareArray A ( intArray B nil ) )(at level 96).
Notation "'Function' A '(' B ')' '{' C '}'" := (declFunction A B C) (at level 96).
Notation "'Struct' A { B1 ';;' B2 ';;' .. ';;' Bn ';;' }" := (declStruct A (cons B1(cons B2 .. (cons Bn nil) ..))) (at level 96).
Notation "'main()' '{' A '}'" := (declMain A) (at level 99).
Notation "'global' A " := (declGlobal A) (at level 96).
Notation "A ;;; B " := (sequencer A B) (at level 96).

Check declareNat "test".
Check declFunction "a"  ["b"] (declareInt "c").
(* Check Function "name" ( ["param1"] ) { (declareString "cevasir") }. *)
Check String "name".
Check String "name" ;; ("test" :s:= "no").
Check If ( 2 >=' 3 ) {"a" :b:= btrue}.
Check While ( "a" <' 4 ) { "a" :n:= "a" ++'}.
Check Bool "flag" ;; Switch (2 +' 2) : { Case (4): {"flag" :b:= btrue} ; Default : {"flag" :b:= bfalse}}.
Check For (int "i";; ("i" :i:= 10);"i" >=' 0;"i" :i:= "i"++') {"a" :i:= "a" +' "i"}.
(*Check (int "array" [ 100 ] { (integ 3) ; (integ 3) ; (integ 3) }).*)
(*Check int "array" [100].*)

Definition Env := Variables -> Val.
Definition env1 : Env := fun x => undecl.
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
 | integers x => match b with
            | integers x => true
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
 | arrays x => match b with
            | arrays x => true
            | _ => false
            end
 | code x => match b with
            | code x => true
            | _ => false
            end
 end.
 
 Definition update (env : Env)(x : string)(v : Val) : Env :=
 fun y =>
  if (string_beq x y) then
    if (andb (checkTypeEquality (env y) unassign) true) then v
    else if (andb (checkTypeEquality (env y) v) true) then v else 
    if (andb (checkTypeEquality (env y) def) true) then v else unassign
  else (env y).
    