(*Chestii triviale: variabile, if, for, while, alte chestii facute la lab/curs
Netriviale: strings, arrays, functions iterative/recursive, structs (maybe classes 
+ methods), switch - case, ternary operator, variable types?*)

Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.

Inductive AExp :=
| const : nat -> AExp
| var : string -> AExp
| plus : AExp -> AExp -> AExp
| minus : AExp -> AExp -> AExp
| times : AExp -> AExp -> AExp
| divide : AExp -> AExp -> AExp
| modulus : AExp -> AExp -> AExp.

Coercion const : nat >-> AExp.
Coercion var : string >-> AExp.
Notation "A +' B" := (plus A B) (at level 50).
Notation "A ++'" := (plus A 1) (at level 50).
Notation "A -' B" := (minus A B) (at level 50).
Notation "A --'" := (minus A 1) (at level 50).
Notation "A *' B" := (times A B) (at level 48).
Notation "A **'" := (times A A) (at level 48).
Notation "A /' B" := (divide A B) (at level 48).
Notation "A %' B" := (modulus A B) (at level 48).

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

Definition Params := list string.
Inductive State :=
| declareNat : string -> State
| assignNat : string -> AExp -> State
| declareBool : string -> State
| assignBool : string -> BExp -> State
| callFunction : string -> Params -> State
| sequence : State -> State -> State
| while : BExp -> State -> State
| ifthen : BExp -> State -> State
| ifelse : BExp -> State -> State -> State.







