Require Import Strings.String.
Local Open Scope string_scope. 
Scheme Equality for string.

Inductive bool_var : Type :=
  | errBool: bool_var
  | boolVal: bool -> bool_var.

Inductive nat_var : Type :=
  | errNat: nat_var
  | natVal: nat -> nat_var.

Inductive str_var : Type :=
  | errString: str_var
  | stringVal: string -> str_var.

Coercion natVal : nat >-> nat_var.
Coercion boolVal : bool >-> bool_var.

Inductive Exp:=
  | bool_const: bool_var -> Exp
  | nat_const: nat_var -> Exp
  | str_const: str_var -> Exp
  | var_: string -> Exp
  | add: Exp -> Exp -> Exp
  | diff: Exp -> Exp -> Exp
  | mul: Exp -> Exp -> Exp
  | div: Exp -> Exp -> Exp
  | modulo: Exp -> Exp -> Exp
  | not_b: Exp -> Exp
  | and_b: Exp -> Exp -> Exp
  | or_b: Exp -> Exp -> Exp
  | lessthan: Exp -> Exp -> Exp
  | lessthaneq: Exp -> Exp -> Exp
  | gtthan: Exp-> Exp -> Exp
  | gtthaneq: Exp -> Exp -> Exp
  | eq_b: Exp -> Exp -> Exp
  | neq_b: Exp -> Exp -> Exp
  | str_concat: str_var -> str_var -> Exp.

Coercion bool_const : bool_var >-> Exp.
Coercion nat_const : nat_var >-> Exp.
Coercion str_const : str_var >-> Exp.
Coercion var_ : string >-> Exp.

Notation "A +' B" := (add A B)(at level 50, left associativity).
Notation "A -' B" := (diff A B)(at level 50, left associativity).
Notation "A *' B" := (mul A B)(at level 49, left associativity).
Notation "A /' B" := (div A B)(at level 49, left associativity).
Notation "A %' B" := (modulo A B)(at level 49, left associativity).
Notation "!' A" := (not_b A) (at level 45, right associativity).
Notation "A &&' B" := (and_b A B) (at level 55, left associativity).
Notation "A ||' B" := (or_b A B) (at level 56, left associativity).
Notation "A <' B" := (lessthan A B) (at level 52, left associativity).
Notation "A <=' B" := (lessthaneq A B) (at level 52, left associativity).
Notation "A >' B" := (gtthan A B) (at level 52, left associativity).
Notation "A >=' B" := (gtthaneq A B) (at level 52, left associativity).
Notation "A ==' B" := (eq_b A B) (at level 53, left associativity).
Notation "A !=' B" := (neq_b A B) (at level 53, left associativity).
Notation "S0 +' +' S1" := (str_concat S0 S1) (at level 50, left associativity).