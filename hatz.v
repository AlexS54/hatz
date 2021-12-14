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
  | arr_a_element: string -> AExp -> AExp
  | struct_a_member: string -> string -> AExp
  | function_a_return: string -> AExp.

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
  | arr_b_element: string -> AExp -> BExp
  | struct_b_member: string -> string -> BExp
  | function_b_return: string -> BExp.

Inductive SExp :=
  | var_s : string -> SExp
  | default_s: defaultStr -> SExp
  | str_concat: SExp -> SExp -> SExp
  | arr_s_element: string -> AExp -> SExp
  | struct_s_member: string -> string -> SExp
  | function_s_return: string -> SExp.

Inductive Stmt :=
  | assgn_n : string -> AExp -> Stmt
  | assgn_b : string -> BExp -> Stmt
  | assgn_s : string -> SExp -> Stmt
  | assgn_arr_n : string -> AExp -> AExp -> Stmt
  | assgn_arr_b : string -> AExp -> BExp -> Stmt
  | assgn_arr_s : string -> AExp -> SExp -> Stmt
  | assgn_str_n : string -> string -> AExp -> Stmt
  | assgn_str_b : string -> string -> BExp -> Stmt
  | assgn_str_s : string -> string -> SExp -> Stmt
  | def_f: string -> Stmt -> Stmt
  | seq : Stmt -> Stmt -> Stmt
  | while : BExp -> Stmt -> Stmt
  | ifthen : BExp -> Stmt -> Stmt
  | ifelse : BExp -> Stmt -> Stmt -> Stmt
  | switch_case : AExp -> list Case -> Stmt
    with Case :=
      | default_case : Stmt -> Case
      | case__ : AExp -> Stmt -> Case.

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
Notation "'get_a' S [ N ]" := (arr_a_element S N) (at level 41).

Notation "!' A" := (not_b A) (at level 45, right associativity).
Notation "A &&' B" := (and_b A B) (at level 55, left associativity).
Notation "A ||' B" := (or_b A B) (at level 56, left associativity).
Notation "A <' B" := (lessthan A B) (at level 52, left associativity).
Notation "A <=' B" := (lessthaneq A B) (at level 52, left associativity).
Notation "A >' B" := (gtthan A B) (at level 52, left associativity).
Notation "A >=' B" := (gtthaneq A B) (at level 52, left associativity).
Notation "A ==' B" := (eq_b A B) (at level 53, left associativity).
Notation "A !=' B" := (neq_b A B) (at level 53, left associativity).
Notation "'get_b' S [ N ]" := (arr_b_element S N) (at level 41).

Notation "S0 +' +' S1" := (str_concat S0 S1) (at level 50, left associativity).
Notation "'get_s' S [ N ]" := (arr_s_element S N) (at level 41).

Notation "'get_a' S .' A" := (struct_a_member S A) (at level 40, left associativity).
Notation "'get_b' S .' A" := (struct_b_member S A) (at level 40, left associativity).
Notation "'get_s' S .' A" := (struct_s_member S A) (at level 40, left associativity).
Notation "'get_a' S ( P0 ',' P1 ',' .. ',' Pn )" := (function_a_return S (cons P0(cons P1 .. (cons Pn nil) ..))) (at level 41).
Notation "'get_b' S ( P0 ',' P1 ',' .. ',' Pn )" := (function_b_return S (cons P0(cons P1 .. (cons Pn nil) ..))) (at level 41).
Notation "'get_s' S ( P0 ',' P1 ',' .. ',' Pn )" := (function_s_return S (cons P0(cons P1 .. (cons Pn nil) ..))) (at level 41).

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

Notation "'nat_' S .' M ::= X" := (assgn_str_n S M X) (at level 80).
Notation "'bool_' S .' M ::= X" := (assgn_str_b S M X) (at level 80).
Notation "'str_' S .' M ::= X" := (assgn_str_s S M X) (at level 80).

Notation "'func_' F '()' { S }" := (def_f F S) (at level 81).

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

Definition NStrEnv := string -> string -> nat.
Definition BStrEnv := string -> string -> bool.
Definition SStrEnv := string -> string -> string.

Definition FEnv := string -> Stmt.

Inductive Env :=
  | env_pack : NEnv -> BEnv -> SEnv -> NArrEnv -> BArrEnv -> SArrEnv -> NStrEnv -> BStrEnv -> SStrEnv -> FEnv -> Env.

Definition def_nenv : NEnv :=
  fun var => 0.

Definition def_benv : BEnv :=
  fun var => false.

Definition def_senv : SEnv :=
  fun var => "".

Definition def_narrenv : NArrEnv :=
  fun var idx => 0.

Definition def_barrenv : BArrEnv :=
  fun var idx => false.

Definition def_sarrenv : SArrEnv :=
  fun var idx => "".

Definition def_nstrenv : NStrEnv :=
  fun var memb => 0.

Definition def_bstrenv : BStrEnv :=
  fun var memb => false.

Definition def_sstrenv : SStrEnv :=
  fun var memb => "".

Definition def_fenv : FEnv :=
  fun name_ => (assgn_n "return" 0).

Definition def_env : Env := env_pack def_nenv def_benv def_senv def_narrenv def_barrenv def_sarrenv def_nstrenv def_bstrenv def_sstrenv def_fenv.

Definition FUpdate (env : FEnv) (name_ : string) (stmts : Stmt) : FEnv :=
  fun name' => if (eqb name_ name')
               then stmts
               else (env name').
 
Definition NUpdate (env : NEnv) (var : string) (value : nat) : NEnv :=
  fun var' => if (eqb var' var)
                then value
                else (env var').

Definition NArrUpdate (env : NArrEnv) (var : string) (index : nat) (value : nat) : NArrEnv :=
  fun var' index' => if (andb (eqb var' var) (Nat.eqb index index'))
                     then value
                     else (env var' index').

Definition NStrUpdate (env : NStrEnv) (var : string) (memb : string) (value : nat) : NStrEnv :=
  fun var' memb' => if (andb (eqb var' var) (eqb memb memb'))
                     then value
                     else (env var' memb').

Definition BUpdate (env : BEnv) (var : string) (value : bool) : BEnv :=
  fun var' => if (eqb var' var)
                then value
                else (env var').

Definition BArrUpdate (env : BArrEnv) (var : string) (index : nat) (value : bool) : BArrEnv :=
  fun var' index' => if (andb (eqb var' var) (Nat.eqb index index'))
                     then value
                     else (env var' index').

Definition BStrUpdate (env : BStrEnv) (var : string) (memb : string) (value : bool) : BStrEnv :=
  fun var' memb' => if (andb (eqb var' var) (eqb memb memb'))
                     then value
                     else (env var' memb').

Definition SUpdate (env : SEnv) (var : string) (value : string) : SEnv :=
  fun var' => if (eqb var' var)
                then value
                else (env var').

Definition SArrUpdate (env : SArrEnv) (var : string) (index : nat) (value : string) : SArrEnv :=
  fun var' index' => if (andb (eqb var' var) (Nat.eqb index index'))
                     then value
                     else (env var' index').

Definition SStrUpdate (env : SStrEnv) (var : string) (memb : string) (value : string) : SStrEnv :=
  fun var' memb' => if (andb (eqb var' var) (eqb memb memb'))
                     then value
                     else (env var' memb').

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

Fixpoint AEval (a : AExp) (env : Env) : nat :=
  match env with
  | env_pack nenv benv senv narrenv barrenv sarrenv nstrenv bstrenv sstrenv fenv =>
  match a with
    | var_a var => nenv var
    | default_a def_ => match def_ with
                          | error_nat => 0
                          | natural n => n 
                        end
    | add a0 a1 => (AEval a0 env) + (AEval a1 env)
    | diff a0 a1 => (AEval a0 env) - (AEval a1 env)
    | mul a0 a1 => (AEval a0 env) * (AEval a1 env)
    | div a0 a1 => Nat.div (AEval a0 env) (AEval a1 env)
    | modulo a0 a1 => Nat.modulo (AEval a0 env) (AEval a1 env)
    | arr_a_element arr idx => narrenv arr (AEval idx env)
    | struct_a_member s0 s1 => nstrenv s0 s1
    | function_a_return name_ => 0
  end
  end.
  
Fixpoint BEval (b : BExp) (env : Env) : bool :=
  match env with
    | env_pack nenv benv senv narrenv barrenv sarrenv nstrenv bstrenv sstrnev fenv =>
  match b with
    | true_b => true
    | false_b => false
    | var_b var => benv var
    | default_b def_ => match def_ with
                          | error_bool => false
                          | boolean bv => bv
                        end
    | not_b b0 => negb (BEval b0 env)
    | and_b b0 b1 => andb (BEval b0 env) (BEval b1 env)
    | or_b b0 b1 => orb (BEval b0 env) (BEval b1 env)
    | lessthan a0 a1 => Nat.leb (AEval a0 env) (AEval a1 env)
    | lessthaneq a0 a1 => orb (Nat.eqb (AEval a0 env) (AEval a1 env)) (Nat.leb (AEval a0 env) (AEval a1 env))
    | gtthan a0 a1 => Nat.leb (AEval a1 env) (AEval a0 env)
    | gtthaneq a0 a1 => orb (Nat.eqb (AEval a0 env) (AEval a1 env)) (Nat.leb (AEval a1 env) (AEval a0 env))
    | eq_b a0 a1 => Nat.eqb (AEval a0 env) (AEval a1 env)
    | neq_b a0 a1 => negb (Nat.eqb (AEval a0 env) (AEval a1 env))
    | arr_b_element arr idx => barrenv arr (AEval idx env)
    | struct_b_member s0 s1 => bstrenv s0 s1
    | function_b_return name_ => false
  end
  end.

Fixpoint SEval (s : SExp) (env : Env) : string :=
  match env with
    | env_pack nenv benv senv narrenv barrenv sarrenv nstrenv bstrenv sstrenv fenv =>
  match s with
    | var_s var => senv var
    | default_s def_ => match def_ with
                          | error_str => ""
                          | str sv => sv
                        end
    | str_concat s0 s1 => (SEval s0 env) ++ (SEval s1 env)
    | arr_s_element arr idx => sarrenv arr (AEval idx env)
    | struct_s_member s0 s1 => sstrenv s0 s1
    | function_s_return name_ => ""
  end
  end.
 
Fixpoint eval (s : Stmt) (env : Env) (gas : nat) : Env :=
  match gas with
    | 0 => env
    | S gas' => match env with
      | env_pack nenv benv senv narrenv barrenv sarrenv nstrenv bstrenv sstrenv fenv => match s with
          | assgn_n var a => env_pack (NUpdate nenv var (AEval a env)) benv senv narrenv barrenv sarrenv nstrenv bstrenv sstrenv fenv
          | assgn_b var b => env_pack nenv (BUpdate benv var (BEval b env)) senv narrenv barrenv sarrenv nstrenv bstrenv sstrenv fenv
          | assgn_s var s => env_pack nenv benv (SUpdate senv var (SEval s env)) narrenv barrenv sarrenv nstrenv bstrenv sstrenv fenv
          | assgn_arr_n arr idx a => env_pack nenv benv senv (NArrUpdate narrenv arr (AEval idx env) (AEval a env)) barrenv sarrenv nstrenv bstrenv sstrenv fenv
          | assgn_arr_b arr idx b => env_pack nenv benv senv narrenv (BArrUpdate barrenv arr (AEval idx env) (BEval b env)) sarrenv nstrenv bstrenv sstrenv fenv
          | assgn_arr_s arr idx s => env_pack nenv benv senv narrenv barrenv (SArrUpdate sarrenv arr (AEval idx env) (SEval s env)) nstrenv bstrenv sstrenv fenv
          | assgn_str_n strc memb a => env_pack nenv benv senv narrenv barrenv sarrenv (NStrUpdate nstrenv strc memb (AEval a env)) bstrenv sstrenv fenv
          | assgn_str_b strc memb b => env_pack nenv benv senv narrenv barrenv sarrenv nstrenv (BStrUpdate bstrenv strc memb (BEval b env)) sstrenv fenv
          | assgn_str_s strc memb s => env_pack nenv benv senv narrenv barrenv sarrenv nstrenv bstrenv (SStrUpdate sstrenv strc memb (SEval s env)) fenv
          | seq s0 s1 => eval s0 (eval s1 env gas') gas'
          | while cond s => if (BEval cond env)
                            then eval (seq s (while cond s)) env gas'
                            else env
          | ifthen b s => if (BEval b env)
                          then eval s env gas'
                          else env
          | ifelse b s0 s1 => if (BEval b env)
                              then eval s0 env gas'
                              else eval s1 env gas'
          | switch_case a0 case_list => match case_list with
                                        | nil => env
                                        | c :: rest_of_list => match c with
                                                      | default_case s => env
                                                      | case__ a1 s => if (BEval (eq_b a0 a1) env)
                                                                     then eval s env gas'
                                                                     else eval (switch_case a0 rest_of_list) env gas'
                                                      end
                                       end
          | def_f name_ stmts => env_pack nenv benv senv narrenv barrenv sarrenv nstrenv bstrenv sstrenv (FUpdate fenv name_ stmts)
          end
      end
  end.

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
  } ;;

  str_ "return" ::= "haeta"
.

Compute (SEval (var_s "return") (eval (test_stmt) def_env 100)).
