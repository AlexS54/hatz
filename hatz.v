Require Import Strings.String.
Require Import List.
Local Open Scope string_scope. 
Scheme Equality for string.

Inductive defaultNat :=
  | error_nat : defaultNat
  | natural : nat -> defaultNat.

Inductive defaultBool :=
  | error_bool : defaultBool
  | boolean : bool -> defaultBool.

Inductive defaultStr :=
  | error_str : defaultStr
  | str : string -> defaultStr.

Coercion natural : nat >-> defaultNat.
Coercion boolean : bool >-> defaultBool.
Coercion str : string >-> defaultStr.

Inductive AExp :=
  | var_a: string -> AExp
  | default_a: defaultNat -> AExp
  | add: AExp -> AExp -> AExp
  | diff: AExp -> AExp -> AExp
  | mul: AExp -> AExp -> AExp
  | div: AExp -> AExp -> AExp
  | modulo: AExp -> AExp -> AExp
  | arr_a_element: string -> defaultNat -> AExp.

Inductive BExp:=
  | true_b
  | false_b
  | var_b: string -> BExp
  | default_b: defaultBool -> BExp
  | not_b: BExp -> BExp
  | and_b: BExp -> BExp -> BExp
  | or_b: BExp -> BExp -> BExp
  | lessthan: AExp -> AExp -> BExp
  | lessthaneq: AExp -> AExp -> BExp
  | gtthan: AExp-> AExp -> BExp
  | gtthaneq: AExp -> AExp -> BExp
  | eq_b: AExp -> AExp -> BExp
  | neq_b: AExp -> AExp -> BExp
  | arr_b_element: string -> defaultNat -> BExp.

Inductive SExp :=
  | var_s : string -> SExp
  | default_s: defaultStr -> SExp
  | str_concat: SExp -> SExp -> SExp
  | arr_s_element: string -> defaultNat -> SExp.

Inductive Exp :=
  | struct_member : string -> string -> Exp
  | call_function : string -> list Exp -> Exp.

Inductive Stmt :=
  | assgn_n : string -> AExp -> Stmt
  | assgn_b : string -> BExp -> Stmt
  | assgn_s : string -> SExp -> Stmt
  | decl_arr_n : string -> AExp -> Stmt
  | decl_arr_b : string -> AExp -> Stmt
  | decl_arr_s : string -> AExp -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | ifelse : BExp -> Stmt -> Stmt -> Stmt
  | switch_case : AExp -> list Case -> Stmt
    with Case :=
      | default : Stmt -> Case
      | case : AExp -> Stmt -> Case.

Inductive Func :=
  | def_n : string -> list Param -> Stmt -> Func
  | def_b : string -> list Param -> Stmt -> Func
  | def_s : string -> list Param -> Stmt -> Func
  with Param :=
    | param_n : string -> Param
    | param_b : string -> Param
    | param_s : string -> Param.

Inductive Struct :=
  | def_struct : string -> list Member -> Struct
  with Member :=
    | member_n : string -> Member
    | member_b : string -> Member
    | member_s : string -> Member.

Coercion default_a : defaultNat >-> AExp.
Coercion var_a : string >-> AExp.

Coercion default_b : defaultBool >-> BExp.
Coercion var_b : string >-> BExp.

Coercion default_s : defaultStr >-> SExp.
Coercion var_s : string >-> SExp.

Notation "A +' B" := (add A B)(at level 50, left associativity).
Notation "A -' B" := (diff A B)(at level 50, left associativity).
Notation "A *' B" := (mul A B)(at level 49, left associativity).
Notation "A /' B" := (div A B)(at level 49, left associativity).
Notation "A %' B" := (modulo A B)(at level 49, left associativity).
Notation "'get_a' S [ N ]" := (arr_a_element S N) (at level 40).

Notation "!' A" := (not_b A) (at level 45, right associativity).
Notation "A &&' B" := (and_b A B) (at level 55, left associativity).
Notation "A ||' B" := (or_b A B) (at level 56, left associativity).
Notation "A <' B" := (lessthan A B) (at level 52, left associativity).
Notation "A <=' B" := (lessthaneq A B) (at level 52, left associativity).
Notation "A >' B" := (gtthan A B) (at level 52, left associativity).
Notation "A >=' B" := (gtthaneq A B) (at level 52, left associativity).
Notation "A ==' B" := (eq_b A B) (at level 53, left associativity).
Notation "A !=' B" := (neq_b A B) (at level 53, left associativity).
Notation "'get_b' S [ N ]" := (arr_b_element S N) (at level 40).

Notation "S0 +' +' S1" := (str_concat S0 S1) (at level 50, left associativity).
Notation "'get_s' S [ N ]" := (arr_s_element S N) (at level 40).

Notation "S .' A" := (struct_member S A) (at level 44, left associativity).
Notation "S ( P0 ',' P1 ',' .. ',' Pn )" := (call_function S (cons P0(cons P1 .. (cons Pn nil) ..))) (at level 41).

Notation "'nat_' X ::= Y" := (assgn_n X Y) (at level 80).
Notation "'bool_' X ::= Y" := (assgn_b X Y) (at level 80).
Notation "'str_' X ::= Y" := (assgn_s X Y) (at level 80).
Notation "A ;; B" := (seq A B) (at level 87).
Notation "'while_' ( B ) { S }" := (while B S) (at level 86).
Notation "'if_' B { S }" := (ifthen B S) (at level 86).
Notation "'if_' B { S0 } 'else_' { S1 }" := (ifelse B S0 S1) (at level 86).
Notation "'default' { S }" := (default S) (at level 85).
Notation "'case' ( A ) { S }" := (case A S) (at level 85).
Notation "'switch' ( A ) { C0  C1  ..  Cn }" := (switch_case A (cons C0(cons C1 .. (cons Cn nil) ..))) (at level 86).

Notation "'nat_' S [ A ]" := (decl_arr_n S A) (at level 80).
Notation "'bool_' S [ A ]" := (decl_arr_b S A) (at level 80).
Notation "'str_' S [ A ]" := (decl_arr_s S A) (at level 80).

Notation "'nat_p' X" := (param_n X) (at level 82).
Notation "'bool_p' X" := (param_b X) (at level 82).
Notation "'str_p' X" := (param_s X) (at level 82).
Notation "'nat_f' F ( P0 ',' P1 ',' .. ',' Pn ) { S }" := (def_n F (cons P0(cons P1 .. (cons Pn nil) ..)) S) (at level 81).
Notation "'bool_f' F ( P0 ',' P1 ',' .. ',' Pn ) { S }" := (def_n F (cons P0(cons P1 .. (cons Pn nil) ..)) S) (at level 81).
Notation "'str_f' F ( P0 ',' P1 ',' .. ',' Pn ) { S }" := (def_n F (cons P0(cons P1 .. (cons Pn nil) ..)) S) (at level 81).

Notation "'nat_m' X" := (member_n X) (at level 82).
Notation "'bool_m' X" := (member_b X) (at level 82).
Notation "'str_m' X" := (member_s X) (at level 82).
Notation "'struct' S { M0 ';;' M1 ';;' .. ';;' Mn ';;' }" := (def_struct S (cons M0(cons M1 .. (cons Mn nil) ..))) (at level 81).

Definition test_stmt :=
  nat_ "test" [100];;
  nat_ "hatz" ::= get_a "test"[69];;
  nat_ "test" ::= 1337;;
  bool_ "test1" ::= true;;
  str_ "test2" ::= "hatz";;
  str_ "test2" ::= "test2" +'+' "iaeohfg";;

  while_ ("test" >' 0) {
    nat_ "test" ::= "test" -' 1;;
    str_ "test"[2077]
  } ;;

  switch ("test"){
    case (1) {
      str_ "test2" ::= get_s "test"[100]
    }
    case (1337) {
      str_ "test2" ::= "ceva"
    }
    default {
      str_ "test2" ::= "altceva"
    }
  }
.

Definition test_func :=
  nat_f "test_function" # nat_p "param0", bool_p "param1", str_p "param2" #
  {
    str_ "test" ::= "iagefh";;
    nat_ "thing" ::= 124
  }
.
(*
Definition test_struct :=
  struct "test" 
  {
    nat_m "test" ;;
    bool_m "test1" ;;
    str_m "test2" 
  }
.*)
