(*Chestii triviale: variabile, if, for, while, alte chestii facute la lab/curs
Netriviale: strings, arrays, functions iterative/recursive, structs (maybe classes 
+ methods), switch - case, ternary operator, variable types?*)

Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.

Definition Var := string.

Inductive Exp :=
| const : nat -> Exp
| id : Var -> Exp
| plus : Exp -> Exp -> Exp
| minus : Exp -> Exp -> Exp
| times : Exp -> Exp -> Exp
| divide : Exp -> Exp -> Exp
| modulus : Exp -> Exp -> Exp.

Coercion const : nat >-> Exp.
Coercion id : Var >-> Exp.
Notation "A +' B" := (plus A B) (at level 50).
Notation "A -' B" := (minus A B) (at level 50).
Notation "A *' B" := (times A B) (at level 48).
Notation "A /' B" := (divide A B) (at level 48).
Notation "A %' B" := (modulus A B) (at level 48).

Fixpoint interpret (e : Exp) (env : Var -> nat) : nat :=
  match e with
  | const c => c
  | id x => (env x)
  | plus e1 e2 => (interpret e1 env) + (interpret e2 env)
  | minus e1 e2 => (interpret e1 env) - (interpret e2 env)
  | times e1 e2 => (interpret e1 env) * (interpret e2 env)
  | divide e1 e2 => Nat.div (interpret e1 env) (interpret e2 env)
  | modulus e1 e2 => Nat.modulo (interpret e1 env) (interpret e2 env)
  end.
Definition env0 := fun x => if string_dec x "x" then 10 else 0.

Compute (interpret (10 /' 2) env0).