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
  | arr_a_element: string -> AExp -> AExp.

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
  | arr_b_element: string -> AExp -> BExp.

Inductive SExp :=
  | var_s : string -> SExp
  | default_s: defaultStr -> SExp
  | str_concat: SExp -> SExp -> SExp
  | arr_s_element: string -> AExp -> SExp.

Inductive Exp :=
  | struct_member : string -> string -> Exp
  | call_function : string -> list Exp -> Exp.

Inductive Stmt :=
  | assgn_n : string -> AExp -> Stmt
  | assgn_b : string -> BExp -> Stmt
  | assgn_s : string -> SExp -> Stmt
  | assgn_arr_n : string -> AExp -> AExp -> Stmt
  | assgn_arr_b : string -> AExp -> BExp -> Stmt
  | assgn_arr_s : string -> AExp -> SExp -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | ifelse : BExp -> Stmt -> Stmt -> Stmt
  | switch_case : AExp -> list Case -> Stmt
    with Case :=
      | default_case : Stmt -> Case
      | case__ : AExp -> Stmt -> Case.

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
Notation "'default' { S }" := (default_case S) (at level 85).
Notation "'case' ( A ) { S }" := (case__ A S) (at level 85).
Notation "'switch' ( A ) { C0  C1  ..  Cn }" := (switch_case A (cons C0(cons C1 .. (cons Cn nil) ..))) (at level 86).

Notation "'nat_' S [ A ] ::= X" := (assgn_arr_n S A X) (at level 80).
Notation "'bool_' S [ A ] ::= X" := (assgn_arr_b S A X) (at level 80).
Notation "'str_' S [ A ] ::= X" := (assgn_arr_s S A X) (at level 80).

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
  nat_ "test" [100] ::= 1;;
  nat_ "hatz" ::= get_a "test"[69];;
  nat_ "test" ::= 1337;;
  bool_ "test1" ::= true;;
  str_ "test2" ::= "hatz";;
  str_ "test2" ::= "test2" +'+' "iaeohfg";;

  while_ ("test" >' 0) {
    nat_ "test" ::= "test" -' 1;;
    str_ "test"[2077] ::= "eigfhjao"
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

(*Definition test_func :=
  nat_f "test_function" # nat_p "param0", bool_p "param1", str_p "param2" #
  {
    str_ "test" ::= "iagefh";;
    nat_ "thing" ::= 124
  }
.

Definition test_struct :=
  struct "test" 
  {
    nat_m "test" ;;
    bool_m "test1" ;;
    str_m "test2" 
  }
.*)

Definition NEnv := string -> nat.
Definition BEnv := string -> bool.
Definition SEnv := string -> string.

Definition NArrEnv := string -> nat -> nat.
Definition BArrEnv := string -> nat -> bool.
Definition SArrEnv := string -> nat -> string.

Inductive Env :=
  | env_pack : NEnv -> BEnv -> SEnv -> NArrEnv -> BArrEnv -> SArrEnv -> Env.

Definition NUpdate (env : NEnv) (var : string) (value : nat) : NEnv :=
  fun var' => if (eqb var' var)
                then value
                else (env var').

Definition NArrUpdate (env : NArrEnv) (var : string) (index : nat) (value : nat) : NArrEnv :=
  fun var' index' => if (andb (eqb var' var) (Nat.eqb index index'))
                     then value
                     else (env var' index').

Definition BUpdate (env : BEnv) (var : string) (value : bool) : BEnv :=
  fun var' => if (eqb var' var)
                then value
                else (env var').

Definition BArrUpdate (env : BArrEnv) (var : string) (index : nat) (value : bool) : BArrEnv :=
  fun var' index' => if (andb (eqb var' var) (Nat.eqb index index'))
                     then value
                     else (env var' index').

Definition SUpdate (env : SEnv) (var : string) (value : string) : SEnv :=
  fun var' => if (eqb var' var)
                then value
                else (env var').

Definition SArrUpdate (env : SArrEnv) (var : string) (index : nat) (value : string) : SArrEnv :=
  fun var' index' => if (andb (eqb var' var) (Nat.eqb index index'))
                     then value
                     else (env var' index').

Definition env_test : NEnv :=
  fun var => if (string_dec var "hatz") then 69 else 0.

Compute (env_test "hatz").
Compute (env_test "not_hatz").

Definition senv_test : SEnv :=
  fun var => if (string_dec var "hatz") then "gionule" else "".

Compute (senv_test "hatz").
Compute (senv_test "not_hatz").

Definition benv_arr_test : BArrEnv :=
  fun var idx => if (andb (eqb var "testing") (Nat.eqb idx 0)) then true else false.

Compute (benv_arr_test "testing" 0).
Compute ((BArrUpdate benv_arr_test "testing" 0 false) "testing" 0).

Fixpoint AEval (a : AExp) (env : NEnv) (arrenv : NArrEnv) : nat :=
  match a with
    | var_a var => env var
    | default_a def_ => match def_ with
                          | error_nat => 0
                          | natural n => n 
                        end
    | add a0 a1 => (AEval a0 env arrenv) + (AEval a1 env arrenv)
    | diff a0 a1 => (AEval a0 env arrenv) - (AEval a1 env arrenv)
    | mul a0 a1 => (AEval a0 env arrenv) * (AEval a1 env arrenv)
    | div a0 a1 => Nat.div (AEval a0 env arrenv) (AEval a1 env arrenv)
    | modulo a0 a1 => Nat.modulo (AEval a0 env arrenv) (AEval a1 env arrenv)
    | arr_a_element arr idx => arrenv arr (AEval idx env arrenv)
  end.
  
Fixpoint BEval (b : BExp) (benv : BEnv) (barrenv : BArrEnv) (nenv : NEnv) (narrenv : NArrEnv) : bool :=
  match b with
    | true_b => true
    | false_b => false
    | var_b var => benv var
    | default_b def_ => match def_ with
                          | error_bool => false
                          | boolean bv => bv
                        end
    | not_b b0 => negb (BEval b0 benv barrenv nenv narrenv)
    | and_b b0 b1 => andb (BEval b0 benv barrenv nenv narrenv) (BEval b1 benv barrenv nenv narrenv)
    | or_b b0 b1 => orb (BEval b0 benv barrenv nenv narrenv) (BEval b1 benv barrenv nenv narrenv)
    | lessthan a0 a1 => Nat.leb (AEval a0 nenv narrenv) (AEval a1 nenv narrenv)
    | lessthaneq a0 a1 => orb (Nat.eqb (AEval a0 nenv narrenv) (AEval a1 nenv narrenv)) (Nat.leb (AEval a0 nenv narrenv) (AEval a1 nenv narrenv))
    | gtthan a0 a1 => Nat.leb (AEval a1 nenv narrenv) (AEval a0 nenv narrenv)
    | gtthaneq a0 a1 => orb (Nat.eqb (AEval a0 nenv narrenv) (AEval a1 nenv narrenv)) (Nat.leb (AEval a1 nenv narrenv) (AEval a0 nenv narrenv))
    | eq_b a0 a1 => Nat.eqb (AEval a0 nenv narrenv) (AEval a1 nenv narrenv)
    | neq_b a0 a1 => negb (Nat.eqb (AEval a0 nenv narrenv) (AEval a1 nenv narrenv))
    | arr_b_element arr idx => barrenv arr (AEval idx nenv narrenv)
  end.

Fixpoint SEval (s : SExp) (env : SEnv) (arrenv : SArrEnv) (nenv : NEnv) (narrenv : NArrEnv) : string :=
  match s with
    | var_s var => env var
    | default_s def_ => match def_ with
                          | error_str => ""
                          | str sv => sv
                        end
    | str_concat s0 s1 => (SEval s0 env arrenv nenv narrenv) ++ (SEval s1 env arrenv nenv narrenv)
    | arr_s_element arr idx => arrenv arr (AEval idx nenv narrenv)
  end.
  
Fixpoint eval (s : Stmt) (env : Env) (gas : nat) : Env :=
  match gas with
    | 0 => env
    | S gas' => match env with
      | env_pack nenv benv senv narrenv barrenv sarrenv => match s with
          | assgn_n var a => env_pack (NUpdate nenv var (AEval a nenv narrenv)) benv senv narrenv barrenv sarrenv
          | assgn_b var b => env_pack nenv (BUpdate benv var (BEval b benv barrenv nenv narrenv)) senv narrenv barrenv sarrenv
          | assgn_s var s => env_pack nenv benv (SUpdate senv var (SEval s senv sarrenv nenv narrenv)) narrenv barrenv sarrenv
          | assgn_arr_n arr idx a => env_pack nenv benv senv (NArrUpdate narrenv arr (AEval idx nenv narrenv) (AEval a nenv narrenv)) barrenv sarrenv
          | assgn_arr_b arr idx b => env_pack nenv benv senv narrenv (BArrUpdate barrenv arr (AEval idx nenv narrenv) (BEval b benv barrenv nenv narrenv)) sarrenv
          | assgn_arr_s arr idx s => env_pack nenv benv senv narrenv barrenv (SArrUpdate sarrenv arr (AEval idx nenv narrenv) (SEval s senv sarrenv nenv narrenv))
          | seq s0 s1 => eval s0 (eval s1 env gas') gas'
          | while cond s => if (BEval cond benv barrenv nenv narrenv)
                            then eval (seq s (while cond s)) (env_pack nenv benv senv narrenv barrenv sarrenv) gas'
                            else env
          | ifthen b s => if (BEval b benv barrenv nenv narrenv)
                          then eval s env gas'
                          else env
          | ifelse b s0 s1 => if (BEval b benv barrenv nenv narrenv)
                              then eval s0 env gas'
                              else eval s1 env gas'
          | switch_case a0 case_list => match case_list with
                                        | nil => env
                                        | c :: rest_of_list => match c with
                                                      | default_case s => env
                                                      | case__ a1 s => if (BEval (eq_b a0 a1) benv barrenv nenv narrenv)
                                                                     then eval s env gas'
                                                                     else eval (switch_case a0 rest_of_list) env gas'
                                                      end
                                       end
          end
      end
  end.
