(* term-project.v *)
(* FPP 2021 - YSC3236 2021-2022, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 08 Nov 2021 *)

(* ********** *)

(* Three language processors for arithmetic expressions. *)

(*
   group name:

   student name:
   e-mail address:
   student ID number:

   student name:
   e-mail address:
   student ID number:

   student name:
   e-mail address:
   student ID number:
*)

(* ********** *)

(*

The primary goal of this term project is to prove the following theorem:

  Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).

for

* a source language of arithmetic expressions:

    Inductive arithmetic_expression : Type :=
    | Literal : nat -> arithmetic_expression
    | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
    | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.
    
    Inductive source_program : Type :=
    | Source_program : arithmetic_expression -> source_program.

* a target language of byte-code instructions:

    Inductive byte_code_instruction : Type :=
    | PUSH : nat -> byte_code_instruction
    | ADD : byte_code_instruction
    | SUB : byte_code_instruction.
    
    Inductive target_program : Type :=
    | Target_program : list byte_code_instruction -> target_program.

* a semantics of expressible values:

    Inductive expressible_value : Type :=
    | Expressible_nat : nat -> expressible_value
    | Expressible_msg : string -> expressible_value.

* a source interpreter

    interpret : source_program -> expressible_value

* a compiler

    compile : source_program -> target_program

* a target interpreter

    run : target_program -> expressible_value

The source for errors is subtraction,
since subtracting two natural numbers does not always yield a natural number:
for example, 3 - 2 is defined but not 2 - 3.

You are expected, at the very least:

* to implement a source interpreter
  and to verify that it satisfies its specification

* to implement a target interpreter (i.e., a virtual machine)
  and to verify that it satisfies its specification

* to implement a compiler
  and to verify that it satisfies its specification

* to prove that the diagram commutes, i.e., to show that
  interpreting any given expression
  gives the same result as
  compiling this expression and then running the resulting compiled program

Beyond this absolute minimum, in decreasing importance, it would be good:

* to make a copy of the above in a separate file
  and modify it mutatis mutandis
  so that the three language processors operate from right to left instead of from left to right,

* to write an accumulator-based compiler and to prove that it satisfies the specification,

* to investigate byte-code verification,

* to investigate decompilation, and

* if there is any time left, to prove that each of the specifications specifies a unique function.

Also, feel free to expand the source language and the target language,
e.g., with multiplication, quotient, and modulo.

*)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                        in if q3 <? 10
                           then s2
                           else "00000".

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
| Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
| Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
| Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1:
   a. time permitting, prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
 *)

Theorem there_is_at_most_one_evaluate_function :
  forall eval1 eval2 : arithmetic_expression -> expressible_value,
    specification_of_evaluate eval1 ->
    specification_of_evaluate eval2 ->
    forall ae : arithmetic_expression,
      eval1 ae = eval2 ae.
Proof.
  intros eval1 eval2 S_eval1 S_eval2 ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  destruct S_eval1 as [S_literal1 _].
  destruct S_eval2 as [S_literal2 _].
  rewrite -> (S_literal2 n).
  exact (S_literal1 n).
  destruct (eval2 ae1) eqn:eval2ae1.
  destruct (eval2 ae2) eqn:eval2ae2.
  destruct (eval1 ae1) eqn:eval1ae1.
  destruct (eval1 ae2) eqn:eval1ae2.
  + destruct S_eval1 as [_ [[_ [_ S_plus_n1n2]] _] ].
    destruct S_eval2 as [_ [[_ [_ S_plus_n1n2']] _] ].
    Check (S_plus_n1n2 ae1 ae2 n1 n2 eval1ae1 eval1ae2).
    rewrite -> (S_plus_n1n2 ae1 ae2 n1 n2 eval1ae1 eval1ae2).
    rewrite -> (S_plus_n1n2' ae1 ae2 n n0 eval2ae1 eval2ae2).
    injection IHae1 as IHae1.
    injection IHae2 as IHae2.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  + discriminate IHae2.
  + discriminate IHae1.
  + destruct S_eval1 as [_ [[_ [S_plus_n1s2 _]] _] ].
    destruct S_eval2 as [_ [[_ [S_plus_n1s2' _]] _] ].
    rewrite -> (S_plus_n1s2 ae1 ae2 n s IHae1 IHae2).
    rewrite -> (S_plus_n1s2' ae1 ae2 n s eval2ae1 eval2ae2).
    reflexivity.
  + destruct S_eval1 as [_ [[S_plus_s1 _] _]].
    destruct S_eval2 as [_ [[S_plus_s1' _] _]].
    rewrite -> (S_plus_s1' ae1 ae2 s eval2ae1).
    exact (S_plus_s1 ae1 ae2 s IHae1).
  + destruct (eval2 ae1) eqn:eval2ae1.
    destruct (eval2 ae2) eqn:eval2ae2.
    destruct (eval1 ae1) eqn:eval1ae1.
    destruct (eval1 ae2) eqn:eval1ae2.
    * case (n1 <? n2) eqn:H_n1_n2;
      case (n <? n0) eqn:H_n_n0;
      injection IHae1 as IHae1;
      injection IHae2 as IHae2.
      - destruct S_eval1 as [_ [_ [_ [_ [S_minus_n1n2err _]]]]].
        destruct S_eval2 as [_ [_ [_ [_ [S_minus_n1n2err' _]]]]].
        rewrite -> (S_minus_n1n2err' ae1 ae2 n n0 eval2ae1 eval2ae2 H_n_n0).
        rewrite -> (S_minus_n1n2err ae1 ae2 n1 n2 eval1ae1 eval1ae2 H_n1_n2).
        rewrite -> IHae1.
        rewrite -> IHae2.
        reflexivity.
      - rewrite -> IHae1 in H_n1_n2.
        rewrite -> IHae2 in H_n1_n2.
        rewrite -> H_n_n0 in H_n1_n2.
        discriminate H_n1_n2.
      - rewrite -> IHae1 in H_n1_n2.
        rewrite -> IHae2 in H_n1_n2.
        rewrite -> H_n_n0 in H_n1_n2.
        discriminate H_n1_n2.
      - destruct S_eval1 as [_ [_ [_ [_ [_ S_minus_n1n2]]]]].
        destruct S_eval2 as [_ [_ [_ [_ [_ S_minus_n1n2']]]]].
        rewrite -> (S_minus_n1n2' ae1 ae2 n n0 eval2ae1 eval2ae2 H_n_n0).
        rewrite -> (S_minus_n1n2 ae1 ae2 n1 n2 eval1ae1 eval1ae2 H_n1_n2).
        rewrite -> IHae1.
        rewrite -> IHae2.
        reflexivity.
        * discriminate IHae2.
        * discriminate IHae1.
        * destruct S_eval1 as [_ [_ [_ [S_minus_n1s2 _]]]].
          destruct S_eval2 as [_ [_ [_ [S_minus_n1s2' _]]]].
          rewrite -> (S_minus_n1s2' ae1 ae2 n s eval2ae1 eval2ae2).
          exact (S_minus_n1s2 ae1 ae2 n s IHae1 IHae2).
        * destruct (eval1 ae2) eqn:eval1ae2.
          destruct (eval2 ae2) eqn:eval2ae2.
          destruct S_eval1 as [_ [_ [S_minus_s1 _]]].
          destruct S_eval2 as [_ [_ [S_minus_s1' _]]].
          rewrite -> (S_minus_s1' ae1 ae2 s eval2ae1).
          exact (S_minus_s1 ae1 ae2 s IHae1).
          discriminate IHae2.
          destruct S_eval1 as [_ [_ [S_minus_s1 _]]].
          destruct S_eval2 as [_ [_ [S_minus_s1' _]]].
          rewrite -> (S_minus_s1' ae1 ae2 s eval2ae1).
          exact (S_minus_s1 ae1 ae2 s IHae1).

  Restart.
  
  intros eval1 eval2 S_eval1 S_eval2 ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2];
    ((destruct S_eval1 as [S_literal1 _];
      destruct S_eval2 as [S_literal2 _];
      rewrite -> (S_literal2 n);
      exact (S_literal1 n))
     || (destruct (eval2 ae1) eqn:eval2ae1;
         destruct (eval2 ae2) eqn:eval2ae2;
         destruct (eval1 ae1) eqn:eval1ae1;
         destruct (eval1 ae2) eqn:eval1ae2;
         try discriminate)).
  + destruct S_eval1 as [_ [[_ [_ S_plus_n1n2]] _] ].
    destruct S_eval2 as [_ [[_ [_ S_plus_n1n2']] _] ].
    Check (S_plus_n1n2 ae1 ae2 n1 n2 eval1ae1 eval1ae2).
    rewrite -> (S_plus_n1n2 ae1 ae2 n1 n2 eval1ae1 eval1ae2).
    rewrite -> (S_plus_n1n2' ae1 ae2 n n0 eval2ae1 eval2ae2).
    injection IHae1 as IHae1.
    injection IHae2 as IHae2.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  + destruct S_eval1 as [_ [[_ [S_plus_n1s2 _]] _] ].
    destruct S_eval2 as [_ [[_ [S_plus_n1s2' _]] _] ].
    rewrite -> (S_plus_n1s2 ae1 ae2 n0 s0 eval1ae1 eval1ae2).
    rewrite -> (S_plus_n1s2' ae1 ae2 n s eval2ae1 eval2ae2).
    injection IHae1 as IHae1.
    injection IHae2 as IHae2.
    rewrite -> IHae2.
    reflexivity.
  + destruct S_eval1 as [_ [[S_plus_s1 _] _]].
    destruct S_eval2 as [_ [[S_plus_s1' _] _]].
    rewrite -> (S_plus_s1' ae1 ae2 s eval2ae1).
    rewrite -> (S_plus_s1 ae1 ae2 s0 eval1ae1).
    exact IHae1.
  + destruct S_eval1 as [_ [[S_plus_s1 _] _]].
    destruct S_eval2 as [_ [[S_plus_s1' _] _]].
    rewrite -> (S_plus_s1' ae1 ae2 s eval2ae1).
    rewrite -> (S_plus_s1 ae1 ae2 s1 eval1ae1).
    exact IHae1.
  + case (n1 <? n2) eqn:H_n1_n2;
      case (n <? n0) eqn:H_n_n0;
      injection IHae1 as IHae1;
      injection IHae2 as IHae2.
    ++  destruct S_eval1 as [_ [_ [_ [_ [S_minus_n1n2err _]]]]].
        destruct S_eval2 as  [_ [_ [_ [_ [S_minus_n1n2err' _]]]]].
        rewrite -> (S_minus_n1n2err' ae1 ae2 n n0 eval2ae1 eval2ae2 H_n_n0).
        rewrite -> (S_minus_n1n2err ae1 ae2 n1 n2 eval1ae1 eval1ae2 H_n1_n2).
        rewrite -> IHae1.
        rewrite -> IHae2.
        reflexivity.
    ++ rewrite -> IHae1 in H_n1_n2.
       rewrite -> IHae2 in H_n1_n2.
       rewrite -> H_n_n0 in H_n1_n2.
       discriminate H_n1_n2.
    ++ rewrite -> IHae1 in H_n1_n2.
       rewrite -> IHae2 in H_n1_n2.
       rewrite -> H_n_n0 in H_n1_n2.
       discriminate H_n1_n2.
    ++ destruct S_eval1 as [_ [_ [_ [_ [_ S_minus_n1n2]]]]].
       destruct S_eval2 as  [_ [_ [_ [_ [_ S_minus_n1n2']]]]].
       rewrite -> (S_minus_n1n2' ae1 ae2 n n0 eval2ae1 eval2ae2 H_n_n0).
       rewrite -> (S_minus_n1n2 ae1 ae2 n1 n2 eval1ae1 eval1ae2 H_n1_n2).
       rewrite -> IHae1.
       rewrite -> IHae2.
       reflexivity.
  + destruct S_eval1 as [_ [_ [_ [S_minus_n1s2 _]]]].
    destruct S_eval2 as [_ [_ [_ [S_minus_n1s2' _]]]].
    rewrite -> (S_minus_n1s2' ae1 ae2 n s eval2ae1 eval2ae2).
    rewrite -> (S_minus_n1s2 ae1 ae2 n0 s0 eval1ae1 eval1ae2).
    exact IHae2.
  + destruct S_eval1 as [_ [_ [S_minus_s1 _]]].
    destruct S_eval2 as [_ [_ [S_minus_s1' _]]].
    rewrite -> (S_minus_s1 ae1 ae2 s0 eval1ae1).
    rewrite -> (S_minus_s1' ae1 ae2 s eval2ae1).
    injection IHae1 as IHae1.
    rewrite -> IHae1.
    reflexivity.
  + destruct S_eval1 as [_ [_ [S_minus_s1 _]]].
    destruct S_eval2 as [_ [_ [S_minus_s1' _]]].
    rewrite -> (S_minus_s1 ae1 ae2 s1 eval1ae1).
    rewrite -> (S_minus_s1' ae1 ae2 s eval2ae1).
    injection IHae1 as IHae1.
    rewrite -> IHae1.
    reflexivity.
Qed.

Fixpoint evaluate (ae: arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
    Expressible_nat n
  | Plus ae1 ae2  =>
    match evaluate ae1 with
    | Expressible_msg s1 => Expressible_msg s1
    | Expressible_nat n1 => match evaluate ae2 with
                            | Expressible_msg s2 => Expressible_msg s2
                            | Expressible_nat n2 => Expressible_nat (n1 + n2)
                            end
    end
  | Minus ae1 ae2  =>
    match evaluate ae1 with
    | Expressible_msg s1 => Expressible_msg s1
    | Expressible_nat n1 => match evaluate ae2 with
                            | Expressible_msg s2 => Expressible_msg s2
                            | Expressible_nat n2 =>
                              if n1 <? n2
                              then Expressible_msg
                                     (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
                              else Expressible_nat (n1 - n2)
                            end
    end
  end.

Lemma fold_unfold_evaluate_Literal :
  forall (n : nat),
    evaluate (Literal n) =
    Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Plus ae1 ae2) =
    match evaluate ae1 with
    | Expressible_msg s1 => Expressible_msg s1
    | Expressible_nat n1 => match evaluate ae2 with
                            | Expressible_msg s2 => Expressible_msg s2
                            | Expressible_nat n2 => Expressible_nat (n1 + n2)
                            end
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Minus ae1 ae2) =
    match evaluate ae1 with
    | Expressible_msg s1 => Expressible_msg s1
    | Expressible_nat n1 => match evaluate ae2 with
                            | Expressible_msg s2 => Expressible_msg s2
                            | Expressible_nat n2 =>
                              if n1 <? n2
                              then Expressible_msg
                                     (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
                              else Expressible_nat (n1 - n2)
                            end
    end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Theorem evaluate_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate; split.
  - exact (fold_unfold_evaluate_Literal).
  - split; split.
    (* case: evaluate ae1 = Expressible_msg s1 *)
    + intros ae1 ae2 s2 H_ae1. 
      Check (fold_unfold_evaluate_Plus ae1 ae2).
      rewrite -> (fold_unfold_evaluate_Plus ae1 ae2).
      rewrite -> H_ae1.
      reflexivity.
    + split.
      (* case: evaluate ae2 = Expressible_msg s2 *)  
      * intros ae1 ae2 n1 s2 H_ae1 H_ae2. 
        rewrite -> (fold_unfold_evaluate_Plus ae1 ae2).
        rewrite -> H_ae1.
        rewrite -> H_ae2.
        reflexivity.
      (* case: evaluate ae1 = Expressible_nat n1 and evaluate ae2 = Expressible_nat n2 *)
      * intros ae1 ae2 n1 n2 H_ae1 H_ae2.
        rewrite -> (fold_unfold_evaluate_Plus ae1 ae2).
        rewrite -> H_ae1.
        rewrite -> H_ae2.
        reflexivity.
    (* case: evaluate ae1 = Expressible_msg s1 *)
    + intros ae1 ae2 s2 H_ae1. 
      Check (fold_unfold_evaluate_Minus ae1 ae2).
      rewrite -> (fold_unfold_evaluate_Minus ae1 ae2).
      rewrite -> H_ae1.
      reflexivity.
    + split.
      (* case: evaluate ae2 = Expressible_msg s2 *) 
      * intros ae1 ae2 n1 s2 H_ae1 H_ae2.  
        rewrite -> (fold_unfold_evaluate_Minus ae1 ae2).
        rewrite -> H_ae1.
        rewrite -> H_ae2.
        reflexivity.
      * split.
        (* case: evaluate ae1 = Expressible_nat n1 and evaluate ae2 = Expressible_nat n2 and n1 ?< n2 = true*)
        -- intros ae1 ae2 n1 n2 H_ae1 H_ae2 H_n1_n2. 
           rewrite -> (fold_unfold_evaluate_Minus ae1 ae2).
           rewrite -> H_ae1.
           rewrite -> H_ae2.
           rewrite -> H_n1_n2.
           reflexivity.
        (* case: evaluate ae1 = Expressible_nat n1 and evaluate ae2 = Expressible_nat n2 and n1?< n2 = false*)
        -- intros ae1 ae2 n1 n2 H_ae1 H_ae2 H_n1_n2. 
           rewrite -> (fold_unfold_evaluate_Minus ae1 ae2).
           rewrite -> H_ae1.
           rewrite -> H_ae2.
           rewrite -> H_n1_n2.
           reflexivity.
  
  Restart.

  
  unfold specification_of_evaluate.
  repeat split; intros ae1 ae2;
    (rewrite -> (fold_unfold_evaluate_Literal) ||
     rewrite -> (fold_unfold_evaluate_Plus) ||
     rewrite -> (fold_unfold_evaluate_Minus)).
  - intros s1 H_evaluate_ae1.
    rewrite -> H_evaluate_ae1.
    reflexivity.
  - intros n1 n2 H_evaluate_ae1 H_evaluate_ae2.
    rewrite -> H_evaluate_ae1.
    rewrite -> H_evaluate_ae2.
    reflexivity.
  - intros n1 n2 H_evaluate_ae1 H_evaluate_ae2.
    rewrite -> H_evaluate_ae1.
    rewrite -> H_evaluate_ae2.
    reflexivity.
  - intros s1 H_evaluate_ae1.
    rewrite -> H_evaluate_ae1.
    reflexivity.
  - intros n1 n2 H_evaluate_ae1 H_evaluate_ae2.
    rewrite -> H_evaluate_ae1.
    rewrite -> H_evaluate_ae2.
    reflexivity.
  - intros n1 n2 H_evaluate_ae1 H_evaluate_ae2 H_lesser_than.
    rewrite -> H_evaluate_ae1.
    rewrite -> H_evaluate_ae2.
    rewrite -> H_lesser_than.
    reflexivity.
  - intros n1 n2 H_evaluate_ae1 H_evaluate_ae2 H_lesser_than.
    rewrite -> H_evaluate_ae1.
    rewrite -> H_evaluate_ae2.
    rewrite -> H_lesser_than.
    reflexivity.

    Restart. (* automatise the proof *)
    
    unfold specification_of_evaluate.
    split.
    intro n.
    rewrite -> fold_unfold_evaluate_Literal.
    reflexivity.
    repeat split;
      intros ae1 ae2;
      (rewrite -> (fold_unfold_evaluate_Plus) ||
       rewrite -> (fold_unfold_evaluate_Minus));
      ((intros s1 H_evaluate_ae1;
        rewrite -> H_evaluate_ae1; reflexivity) ||
       (intros n1 n2 H_evaluate_ae1 H_evaluate_ae2;
        rewrite -> H_evaluate_ae1;
        rewrite -> H_evaluate_ae2;  reflexivity) ||
       (intros n1 n2 H_evaluate_ae1 H_evaluate_ae2 H_lesser_than;
        rewrite -> H_evaluate_ae1;
        rewrite -> H_evaluate_ae2;
        rewrite -> H_lesser_than; reflexivity)).
Qed.

Theorem there_is_at_most_one_interpret_function :
  forall itpt1 itpt2 : source_program -> expressible_value,
    specification_of_interpret itpt1 ->
    specification_of_interpret itpt2 ->
    forall sp : source_program,
      itpt1 sp = itpt2 sp.
Proof.
  intros itpt1 itpt2 spec_i1 spec_i2 sp.
  unfold specification_of_interpret in spec_i1, spec_i2.
  destruct sp as [ae].
  rewrite -> (spec_i2
                evaluate
                evaluate_satisfies_the_specification_of_evaluate
                ae).
  exact (spec_i1
           evaluate
           evaluate_satisfies_the_specification_of_evaluate
           ae).
Qed. 

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae => evaluate ae
  end.

Theorem interpret_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret, interpret.
  intros eval s_eval ae.
  exact (there_is_at_most_one_evaluate_function
           evaluate
           eval
           evaluate_satisfies_the_specification_of_evaluate
           s_eval
           ae).
Qed.

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
| Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall (n : nat)
          (ds : data_stack),
     decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  ((decode_execute ADD nil = KO "ADD: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute ADD (n2 :: nil) = KO "ADD: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds)))
  /\
  ((decode_execute SUB nil = KO "SUB: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute SUB (n2 :: nil) = KO "SUB: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = true ->
       decode_execute SUB (n2 :: n1 :: ds) = KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = false ->
       decode_execute SUB (n2 :: n1 :: ds) = OK ((n1 - n2) :: ds))).

(* Task 2:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

Theorem there_is_at_most_one_decode_execute :
  forall (decode_execute_1 decode_execute_2 : byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_decode_execute decode_execute_1 ->
    specification_of_decode_execute decode_execute_2 ->
    forall (bcis : byte_code_instruction)
           (ds : data_stack),
      decode_execute_1 bcis ds = decode_execute_2 bcis ds.
Proof.
  intros decode_execute_1 decode_execute_2 S_decode_execute_1 S_decode_execute_2 bcis ds.
  destruct bcis;
    unfold specification_of_decode_execute in S_decode_execute_1;
    unfold specification_of_decode_execute in S_decode_execute_2.
  - destruct S_decode_execute_1 as [S_PUSH_1 _].
    destruct S_decode_execute_2 as [S_PUSH_2 _].
    rewrite -> (S_PUSH_2 n ds).
    exact (S_PUSH_1 n ds).
  - destruct S_decode_execute_1 as
        [ _ [[S_ADD_nil_1 [S_ADD_cons_1 S_ADD_cons_cons_1]] _]].
    destruct S_decode_execute_2 as
        [ _ [[S_ADD_nil_2 [S_ADD_cons_2 S_ADD_cons_cons_2]] _]].
    destruct ds as [ | n1].
    -- rewrite -> S_ADD_nil_2.
       exact (S_ADD_nil_1).
    -- destruct ds as [ | n2].
       --- rewrite -> (S_ADD_cons_2 n1).
           exact (S_ADD_cons_1 n1).
       --- rewrite -> (S_ADD_cons_cons_2 n2 n1 ds).
           exact (S_ADD_cons_cons_1 n2 n1 ds).
  - destruct S_decode_execute_1 as
        [ _ [_ [S_SUB_nil_1 [S_SUB_cons_1 [S_SUB_cons_cons_lesser_than_1 S_SUB_cons_cons_not_lesser_than_1]]]]].
    destruct S_decode_execute_2 as
        [ _ [_ [S_SUB_nil_2 [S_SUB_cons_2 [S_SUB_cons_cons_lesser_than_2 S_SUB_cons_cons_not_lesser_than_2]]]]].
    destruct ds as [ | n1].
    -- rewrite -> S_SUB_nil_2.
       exact (S_SUB_nil_1).
    -- destruct ds as [ | n2].
       --- rewrite -> (S_SUB_cons_2 n1).
           exact (S_SUB_cons_1 n1).
       --- case (n2 <? n1) eqn:H_n2_n1.
           ---- rewrite -> (S_SUB_cons_cons_lesser_than_2 n2 n1 ds H_n2_n1).
                 exact (S_SUB_cons_cons_lesser_than_1 n2 n1 ds H_n2_n1).
           ---- rewrite -> (S_SUB_cons_cons_not_lesser_than_2 n2 n1 ds H_n2_n1).
                 exact (S_SUB_cons_cons_not_lesser_than_1 n2 n1 ds H_n2_n1).
Qed.

Definition decode_execute (bcis : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | PUSH n =>
    OK (n :: ds)
  | ADD =>
    match ds with
    | nil => KO "ADD: stack underflow"
    | (n2 :: nil) => KO "ADD: stack underflow"
    | (n2 :: n1 :: ds) => OK ((n1 + n2) :: ds)
    end
  | SUB => match ds with
           | nil => KO "SUB: stack underflow"
           | (n2 :: nil) => KO "SUB: stack underflow"
           | (n2 :: n1 :: ds) => if n1 <? n2
                                 then KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
                                 else OK ((n1 - n2) :: ds)
           end
  end.


Theorem decode_execute_satisfies_the_specification_of_decode_execute :
  specification_of_decode_execute decode_execute.
Proof.
    unfold specification_of_decode_execute; split.
  - intros n ds.
    unfold decode_execute.
    reflexivity.
  - split; split.
    + unfold decode_execute.
      reflexivity.
    + split.
      * intro n2.
        unfold decode_execute.
        reflexivity.
      * intros n1 n2 ds.
        unfold decode_execute.
        reflexivity.
    + unfold decode_execute.
      reflexivity.
    + split.
      * intro n2.
        unfold decode_execute.
        reflexivity.
      * split.
        -- intros n1 n2 ds H_n1_n2.
           unfold decode_execute.
           rewrite -> H_n1_n2.
           reflexivity.
        -- intros n1 n2 ds H_n1_n2.
           unfold decode_execute.
           rewrite -> H_n1_n2.
           reflexivity.

  Restart.

  repeat split;
    try reflexivity;
    intros n1 n2 ds H_lesser_than;
    unfold decode_execute;
    rewrite -> H_lesser_than;
    reflexivity.
Qed.

(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  forall decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
        fetch_decode_execute_loop nil ds = OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
        decode_execute bci ds = OK ds' ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
        decode_execute bci ds = KO s ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        KO s).

(* Task 3:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

Theorem there_is_at_most_one_fetch_decode_execute_loop :
  forall (fetch_decode_execute_loop_1 fetch_decode_execute_loop_2 : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_1 ->
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_2 ->
    forall (bcis : list  byte_code_instruction)
           (ds : data_stack),
      fetch_decode_execute_loop_1 bcis ds = fetch_decode_execute_loop_2 bcis ds.
Proof.
  intros fetch_decode_execute_loop_1 fetch_decode_execute_loop_2
         S_fetch_decode_execute_loop_1 S_fetch_decode_execute_loop_2
         bcis.
  unfold specification_of_fetch_decode_execute_loop in S_fetch_decode_execute_loop_1, S_fetch_decode_execute_loop_2.
  destruct (S_fetch_decode_execute_loop_1 decode_execute decode_execute_satisfies_the_specification_of_decode_execute)
    as [H_nil_1 [H_decode_execute_OK_1 H_decode_execute_KO_1]].
   destruct (S_fetch_decode_execute_loop_2 decode_execute decode_execute_satisfies_the_specification_of_decode_execute)
    as [H_nil_2 [H_decode_execute_OK_2 H_decode_execute_KO_2]].
  induction bcis as [ | bci bcis' IHbcis'].
  - intro ds.
    rewrite -> (H_nil_2 ds).
    exact (H_nil_1 ds).
  - intro ds.
    destruct (decode_execute bci ds) as [ds' | s] eqn: H_decode_execute.
    -- rewrite -> (H_decode_execute_OK_1 bci bcis' ds ds' H_decode_execute).
       rewrite -> (H_decode_execute_OK_2 bci bcis' ds ds' H_decode_execute).
       exact (IHbcis' ds').
    -- rewrite -> (H_decode_execute_KO_2 bci bcis' ds s H_decode_execute).
       exact (H_decode_execute_KO_1 bci bcis' ds s H_decode_execute).
Qed.


Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
    match bcis with
    | nil =>
      OK ds
    | bci :: bcis' =>
      match decode_execute bci ds with
      | OK ds' => fetch_decode_execute_loop bcis' ds'
      | KO s => KO s
      end
    end.

Lemma fold_unfold_fetch_decode_execute_loop_nil :
  forall (ds : data_stack),
    fetch_decode_execute_loop nil ds = OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis') ds =
    match decode_execute bci ds with
    | OK ds' => fetch_decode_execute_loop bcis' ds'
    | KO s => KO s
    end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Theorem fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute0 H_decode_execute0_satisfies_the_specification_of_decode_execute.
  split.
  + exact (fold_unfold_fetch_decode_execute_loop_nil).
  + split; intros bci bcis' ds.
    - intros ds' H_decode_execute0. 
      rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci bcis' ds).
      rewrite -> (there_is_at_most_one_decode_execute
                    decode_execute
                    decode_execute0
                    decode_execute_satisfies_the_specification_of_decode_execute
                    H_decode_execute0_satisfies_the_specification_of_decode_execute).
      rewrite -> (H_decode_execute0).
      reflexivity.
  - intros s H_decode_execute0.
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci bcis' ds).
    rewrite -> (there_is_at_most_one_decode_execute
                  decode_execute
                  decode_execute0
                  decode_execute_satisfies_the_specification_of_decode_execute
                  H_decode_execute0_satisfies_the_specification_of_decode_execute).
    rewrite -> (H_decode_execute0).
    reflexivity.
Qed.

(* ********** *)

(* Task 4:
   Prove that for any lists of byte-code instructions bcis1 and bcis2,
   and for any data stack ds,
   executing the concatenation of bcis1 and bcis2 (i.e., bcis1 ++ bcis2) with ds
   gives the same result as
   (1) executing bcis1 with ds, and then
   (2) executing bcis2 with the resulting data stack, if there exists one.
 *)

Lemma fold_unfold_append_nil :
  forall bcis2 : list byte_code_instruction,
    nil ++ bcis2 = bcis2.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_append_cons :
  forall (bci1 : byte_code_instruction)
         (bci1s bci2s : list byte_code_instruction),
    (bci1 :: bci1s) ++ bci2s =
    bci1 :: (bci1s ++ bci2s).
Proof.
  fold_unfold_tactic List.app.
Qed.

Theorem execution_and_concatenation_commute :
  forall (bcis1 bcis2 : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (bcis1 ++ bcis2) ds =
    match fetch_decode_execute_loop bcis1 ds with
    | OK ds_new => fetch_decode_execute_loop bcis2 ds_new
    | KO s => KO s
    end.
Proof.
  intros bcis1 bcis2.
  induction bcis1 as [ | bci1 bcis1' IHbcis1'].
  - intro ds.
    rewrite -> (fold_unfold_append_nil bcis2).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_nil).
    reflexivity.
  - intro ds.
    rewrite -> (fold_unfold_append_cons bci1 bcis1' bcis2).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci1 (bcis1' ++ bcis2) ds).
    rewrite -> (fold_unfold_fetch_decode_execute_loop_cons bci1 bcis1' ds).
    destruct (decode_execute bci1 ds) as [ds' | s'].
    -- exact (IHbcis1' ds').
    -- reflexivity.
Qed.

(* ********** *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop bcis nil = OK nil ->
       run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
       run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
       run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = KO s ->
       run (Target_program bcis) = Expressible_msg s).

(* Task 5:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Proposition there_is_at_most_one_run :
  forall run1 run2 : target_program -> expressible_value,
    specification_of_run run1 ->
    specification_of_run run2 ->
    forall (tp : target_program),           
     run1 tp = run2 tp.
Proof.
  intros run1 run2 S_run1 S_run2 tp.
  destruct tp as [bcis].
  unfold specification_of_run in S_run1.
  Check (S_run1 fetch_decode_execute_loop
                fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop).
  destruct (S_run1 fetch_decode_execute_loop
                   fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop)
    as [H_run1_OK_nil [H_run1_OK_cons [H_run1_OK_cons2 H_run1_KO]]].
  destruct (S_run2 fetch_decode_execute_loop
                   fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop)
    as [H_run2_OK_nil [H_run2_OK_cons [H_run2_OK_cons2 H_run2_KO]]].
  destruct (fetch_decode_execute_loop bcis nil) as [ds | s] eqn:H_fetch_decode_execute_loop.
  - destruct ds as [ | n [ | n' ds']]. (* looking for subsequent cases of ds; nil or n::ds' *)
    + rewrite -> (H_run2_OK_nil bcis H_fetch_decode_execute_loop).
      exact (H_run1_OK_nil bcis H_fetch_decode_execute_loop).
    + rewrite -> (H_run2_OK_cons bcis n H_fetch_decode_execute_loop).
      exact (H_run1_OK_cons bcis n H_fetch_decode_execute_loop).
    + rewrite -> (H_run2_OK_cons2 bcis n n' ds' H_fetch_decode_execute_loop).
      exact (H_run1_OK_cons2 bcis n n' ds' H_fetch_decode_execute_loop).
  - rewrite -> (H_run2_KO bcis s H_fetch_decode_execute_loop). (* consider the case string s *)
    exact (H_run1_KO bcis s H_fetch_decode_execute_loop).
Qed.

Definition run (t : target_program) : expressible_value :=
  match t with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
    | KO s =>
      Expressible_msg s
    | OK ds => 
      match ds with
      | nil => Expressible_msg "no result on the data stack"
      | n :: ds' => 
        match ds' with
        | nil => Expressible_nat n
        | n' :: ds'' => Expressible_msg "too many results on the data stack"
        end
      end
    end
  end.

Theorem run_satisfies_the_specification_of_run :
  specification_of_run run.
Proof.
  unfold specification_of_run.
  intros fetch_decode_execute_loop' S_fetch_decode_execute_loop'.
  Check (there_is_at_most_one_fetch_decode_execute_loop
           fetch_decode_execute_loop'
           fetch_decode_execute_loop
           S_fetch_decode_execute_loop'
           fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop).
  assert (H_at_most_one_fdel := there_is_at_most_one_fetch_decode_execute_loop
                                  fetch_decode_execute_loop'
                                  fetch_decode_execute_loop
                                  S_fetch_decode_execute_loop'
                                  fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop).
  split.
  - intros bcis S_fetch_decode_execute_loop_nil'; unfold run.
    rewrite <- (H_at_most_one_fdel bcis nil).
    rewrite -> S_fetch_decode_execute_loop_nil'.
    reflexivity.
  - split.
    + intros bcis n S_fetch_decode_execute_loop_cons1'; unfold run.
      rewrite <- (H_at_most_one_fdel bcis nil).
      rewrite -> S_fetch_decode_execute_loop_cons1'.
      reflexivity.
    + split.
      * intros bcis n n' ds'' S_fetch_decode_execute_loop_cons2'; unfold run.
        rewrite <- (H_at_most_one_fdel bcis nil).
        rewrite -> S_fetch_decode_execute_loop_cons2'.
        reflexivity.
      * intros bcis s S_fetch_decode_execute_loop_s'; unfold run.
        rewrite <- (H_at_most_one_fdel bcis nil).
        rewrite -> S_fetch_decode_execute_loop_s'.
        reflexivity.

  Restart.

  unfold specification_of_run.
  intros fetch_decode_execute_loop0 S_fetch_decode_execute_loop0.
  repeat split;
    intro bcis;
    rewrite -> (there_is_at_most_one_fetch_decode_execute_loop
                  fetch_decode_execute_loop0 
                  fetch_decode_execute_loop
                  S_fetch_decode_execute_loop0
                  fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop);
    unfold run;
    (intros n n' ds' H_fetch_decode_execute_loop ||
     intros n_or_s H_fetch_decode_execute_loop ||
     intro H_fetch_decode_execute_loop);
    rewrite -> H_fetch_decode_execute_loop;
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).

(* Task 6:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function using list concatenation, i.e., ++; and
   c. verify that your function satisfies the specification.
 *)

Proposition there_is_at_most_one_compile_aux :
  forall (compile_aux1 compile_aux2 : arithmetic_expression -> list byte_code_instruction)
         (ae : arithmetic_expression),
    specification_of_compile_aux compile_aux1 ->
    specification_of_compile_aux compile_aux2 ->
    compile_aux1 ae = compile_aux2 ae.
Proof.
  intros compile_aux1 compile_aux2 ae S_compile_aux1 S_compile_aux2.
  unfold specification_of_compile_aux in S_compile_aux1.
  destruct S_compile_aux1 as [S_compile_aux1_Lit [S_compile_aux1_Plus S_compile_aux1_Minus]].
  destruct S_compile_aux2 as [S_compile_aux2_Lit [S_compile_aux2_Plus S_compile_aux2_Minus]].
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - rewrite -> (S_compile_aux2_Lit n).
    exact (S_compile_aux1_Lit n).
  - rewrite -> (S_compile_aux2_Plus ae1 ae2).
    rewrite -> (S_compile_aux1_Plus ae1 ae2).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
  - rewrite -> (S_compile_aux2_Minus ae1 ae2).
    rewrite -> (S_compile_aux1_Minus ae1 ae2).
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.

  Restart.

  intros compile_aux1 compile_aux2 ae S_compile_aux1 S_compile_aux2.
  unfold specification_of_compile_aux in S_compile_aux1.
  destruct S_compile_aux1 as [S_compile_aux1_Lit [S_compile_aux1_Plus S_compile_aux1_Minus]].
  destruct S_compile_aux2 as [S_compile_aux2_Lit [S_compile_aux2_Plus S_compile_aux2_Minus]].
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2];
  ((rewrite -> (S_compile_aux2_Lit n);
    exact (S_compile_aux1_Lit n))
   || ((rewrite -> (S_compile_aux2_Plus ae1 ae2)
        || rewrite -> (S_compile_aux2_Minus ae1 ae2));
       rewrite <- IHae1;
       rewrite <- IHae2;
       (exact (S_compile_aux1_Plus ae1 ae2)
        || exact (S_compile_aux1_Minus ae1 ae2)))).
Qed.

Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: nil
  | Plus ae1 ae2 =>
    (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil)
  | Minus ae1 ae2 =>
    (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)
  end.

Lemma fold_unfold_compile_aux_Literal :
  forall n : nat,
    compile_aux (Literal n) = PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_Plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_Minus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.    

Theorem compile_aux_satisfies_specification_of_compile_aux :
  specification_of_compile_aux compile_aux.
Proof.
  unfold specification_of_compile_aux.
  split.
  - intro n.
    exact (fold_unfold_compile_aux_Literal n).
  - split.
    + intros ae1 ae2.
      exact (fold_unfold_compile_aux_Plus ae1 ae2).
    + intros ae1 ae2.
      exact (fold_unfold_compile_aux_Minus ae1 ae2).
Qed.


Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Proposition there_is_at_most_one_compile :
  forall (compile1 compile2 : source_program -> target_program)
         (sp : source_program),
    specification_of_compile compile1 ->
    specification_of_compile compile2 ->
    compile1 sp = compile2 sp.
Proof.
  intros compile1 compile2 sp S_compile1 S_compile2.
  destruct sp as [ae].
  unfold specification_of_compile in S_compile2.
  Check (S_compile2 compile_aux compile_aux_satisfies_specification_of_compile_aux ae).
  rewrite -> (S_compile2 compile_aux compile_aux_satisfies_specification_of_compile_aux ae).
  unfold specification_of_compile in S_compile1.
  exact (S_compile1 compile_aux compile_aux_satisfies_specification_of_compile_aux ae).
Qed.

Definition compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_aux ae)
  end.

Theorem compile_satisfies_specification_of_compile :
  specification_of_compile compile.
Proof.
  unfold specification_of_compile.
  intros compile_aux' S_compile_aux' ae.
  unfold compile.
  Check (there_is_at_most_one_compile_aux
           compile_aux
           compile_aux'
           ae
           compile_aux_satisfies_specification_of_compile_aux S_compile_aux').
  rewrite -> (there_is_at_most_one_compile_aux
                compile_aux
                compile_aux'
                ae
                compile_aux_satisfies_specification_of_compile_aux S_compile_aux').
  reflexivity.
Qed.


(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
 *)

Fixpoint compile_aux'  (a : list byte_code_instruction) (ae : arithmetic_expression) : list byte_code_instruction :=
  match ae with
  | Literal n =>
    PUSH n :: a
  | Plus ae1 ae2 =>
    compile_aux' (compile_aux' (ADD :: a) ae2) ae1
  | Minus ae1 ae2 =>
    compile_aux' (compile_aux' (SUB :: a) ae2) ae1
  end.

Lemma fold_unfold_compile_aux'_Literal :
  forall (n : nat)
         (a : list byte_code_instruction),
    compile_aux' a (Literal n) = PUSH n :: a.
Proof.
  fold_unfold_tactic compile_aux'.
Qed.

Lemma fold_unfold_compile_aux'_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_aux' a (Plus ae1 ae2) = compile_aux' (compile_aux' (ADD :: a) ae2) ae1.
Proof.
    fold_unfold_tactic compile_aux'.
Qed.

Lemma fold_unfold_compile_aux'_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
     compile_aux' a (Minus ae1 ae2) = compile_aux' (compile_aux' (SUB :: a) ae2) ae1.
Proof.
    fold_unfold_tactic compile_aux'.
Qed.

Lemma about_compile_aux' :
  forall (ae : arithmetic_expression) (bcis : list byte_code_instruction),
    compile_aux' bcis ae = compile_aux' nil ae ++ bcis.
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2];
    intro bcis.
  - rewrite -> fold_unfold_compile_aux'_Literal.
    rewrite -> fold_unfold_compile_aux'_Literal.
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_append_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux'_Plus.
    rewrite -> (IHae2 (ADD :: bcis)).
    rewrite -> fold_unfold_compile_aux'_Plus.
    rewrite -> (IHae2 (ADD :: nil)).
    rewrite -> (IHae1 (compile_aux' nil ae2 ++ ADD :: bcis)).
    rewrite -> (IHae1 (compile_aux' nil ae2 ++ ADD :: nil)).
    rewrite -> (app_assoc
             (compile_aux' nil ae1)
             (compile_aux' nil ae2) (ADD :: nil)).
    rewrite <- (app_assoc
             (compile_aux' nil ae1 ++ compile_aux' nil ae2)
             (ADD :: nil)
             bcis).
    rewrite -> (fold_unfold_append_cons ADD nil).
    rewrite -> fold_unfold_append_nil.
    rewrite -> app_assoc.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux'_Minus.
    rewrite -> (IHae2 (SUB :: bcis)).
    rewrite -> fold_unfold_compile_aux'_Minus.
    rewrite -> (IHae2 (SUB :: nil)).
    rewrite -> (IHae1 (compile_aux' nil ae2 ++ SUB :: bcis)).
    rewrite -> (IHae1 (compile_aux' nil ae2 ++ SUB :: nil)).
    rewrite -> (app_assoc
             (compile_aux' nil ae1)
             (compile_aux' nil ae2) (SUB :: nil)).
    rewrite <- (app_assoc
             (compile_aux' nil ae1 ++ compile_aux' nil ae2)
             (SUB :: nil)
             bcis).
    rewrite -> (fold_unfold_append_cons SUB nil).
    rewrite -> fold_unfold_append_nil.
    rewrite -> app_assoc.
    reflexivity.
Qed.  

Theorem compile_aux'_satisfies_specification_of_compile_aux :
  specification_of_compile_aux (compile_aux' nil).
Proof.
  unfold specification_of_compile_aux.
  split.
  - intro n.
    exact (fold_unfold_compile_aux'_Literal n nil).
  - split;
      intros ae1 ae2;
      (rewrite -> fold_unfold_compile_aux'_Plus
       || rewrite -> fold_unfold_compile_aux'_Minus);
      rewrite -> (about_compile_aux' ae2);
      rewrite -> (about_compile_aux' ae1);
      reflexivity.
Qed.      

Definition compile' (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>
    Target_program (compile_aux' nil ae)
  end.

Theorem compile'_satisfies_specification_of_compile :
  specification_of_compile compile'.
Proof.
  unfold specification_of_compile.
  intros compile_aux'' S_compile_aux'' ae.
  unfold compile'.
  rewrite -> (there_is_at_most_one_compile_aux
                (compile_aux' nil)
                compile_aux''
                ae
                compile_aux'_satisfies_specification_of_compile_aux S_compile_aux'').
  reflexivity.
Qed.

Corollary compile_and_compile'_are_equivalent :
  forall sp : source_program,
    compile sp = compile' sp.
Proof.
  intro sp.
  Check (there_is_at_most_one_compile
           compile
           compile'
           sp
           compile_satisfies_specification_of_compile
           compile'_satisfies_specification_of_compile).
  exact (there_is_at_most_one_compile
           compile
           compile'
           sp
           compile_satisfies_specification_of_compile
           compile'_satisfies_specification_of_compile).
Qed.

(* ********** *)


(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)

(* this proof cannot be induction because evaluate can only either return a natural number or a sting of numerical underflow 
We had to explicitly define a eureka lemma containing the fact that evaluate ae can indeed
only produce two outputs *)

Lemma about_evaluate_outputs :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (n : nat),
        evaluate ae = Expressible_nat n ->
        fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds))
    /\
    (forall (s : string),
        evaluate ae = Expressible_msg s  ->
        fetch_decode_execute_loop (compile_aux ae) ds = KO s).
Proof.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2];
    intro ds.
  - split.
    + intros n' H_eval_n. (* Literal n, expressible nat *)
      rewrite -> fold_unfold_compile_aux_Literal.
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
      unfold decode_execute.
      rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
      rewrite -> fold_unfold_evaluate_Literal in H_eval_n.
      injection H_eval_n as H_eval_n.
      rewrite -> H_eval_n.
      reflexivity.
    + intros s H_eval_s. (* Literal n, expressible msg *)
      rewrite -> fold_unfold_evaluate_Literal in H_eval_s.
      discriminate.
  - split.
    + intros n' H_eval_n. (* Plus ae1 ae2, expressible nat *)
      rewrite -> fold_unfold_evaluate_Plus in H_eval_n.
      case (evaluate ae1) as [n1 | s1] eqn:eval1.
      * case (evaluate ae2) as [n2 | s2] eqn:eval2.
        -- injection H_eval_n as H_eval_n.
           rewrite -> fold_unfold_compile_aux_Plus.
           rewrite -> execution_and_concatenation_commute.
           destruct (IHae1 ds) as [IHae1_nat IHae1_s].
           rewrite -> (IHae1_nat n1 eq_refl).
           rewrite -> execution_and_concatenation_commute.
           destruct (IHae2 (n1 :: ds)) as [IHae2_nat IHae2_s].
           rewrite -> (IHae2_nat n2 eq_refl).
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           unfold decode_execute.
           rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
           rewrite -> H_eval_n.
           reflexivity.
        -- discriminate.
      * discriminate.
    + intros s H_eval_s. (* Plus ae1 ae2, expressible msg *)
      rewrite -> fold_unfold_evaluate_Plus in H_eval_s.
      case (evaluate ae1) as [n1 | s1] eqn:eval1.
      * case (evaluate ae2) as [n2 | s2] eqn:eval2.
        -- discriminate.
        -- rewrite -> fold_unfold_compile_aux_Plus.
           rewrite -> execution_and_concatenation_commute.
           destruct (IHae1 ds) as [IHae1_nat IHae1_s].
           rewrite -> (IHae1_nat n1 eq_refl).
           rewrite -> execution_and_concatenation_commute.
           destruct (IHae2 (n1 :: ds)) as [IHae2_nat IHae2_s].
           rewrite -> (IHae2_s s H_eval_s).
           reflexivity.
      * rewrite -> fold_unfold_compile_aux_Plus.
        rewrite -> execution_and_concatenation_commute.
        destruct (IHae1 ds) as [IHae1_nat IHae1_s].
        rewrite -> (IHae1_s s1 eq_refl).
        injection H_eval_s as H_eval_s.
        rewrite -> H_eval_s.
        reflexivity.
  - split.
    + intros n H_eval_n. (* minus ae1 ae2 , expressible nat *)
      rewrite -> fold_unfold_evaluate_Minus in H_eval_n.
      case (evaluate ae1) as [n1 | s1] eqn:eval1.
      * case (evaluate ae2) as [n2 | s2] eqn:eval2.
        -- case (n1 <? n2) eqn:n1_n2.
        ++ discriminate.
        ++ injection H_eval_n as H_eval_n.
           rewrite -> fold_unfold_compile_aux_Minus.
           rewrite -> execution_and_concatenation_commute.
           destruct (IHae1 ds) as [IHae1_nat IHae1_s].
           rewrite -> (IHae1_nat n1 eq_refl).
           rewrite -> execution_and_concatenation_commute.
           destruct (IHae2 (n1 :: ds)) as [IHae2_nat IHae2_s].
           rewrite -> (IHae2_nat n2 eq_refl).
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           unfold decode_execute.
           rewrite -> n1_n2.
           rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
           rewrite -> H_eval_n.
           reflexivity.
        -- discriminate.
      * discriminate.
    + intros s H_eval_s. (* Minus ae1 ae2, expresisble msg *)
      rewrite -> fold_unfold_evaluate_Minus in H_eval_s.
      case (evaluate ae1) as [n1 | s1] eqn:eval1.
      * case (evaluate ae2) as [n2 | s2] eqn:eval2.
        -- case (n1 <? n2) eqn:n1_n2.
           ++ rewrite -> fold_unfold_compile_aux_Minus.
              rewrite -> execution_and_concatenation_commute.
              destruct (IHae1 ds) as [IHae1_nat IHae1_s].
              rewrite -> (IHae1_nat n1 eq_refl).
              rewrite -> execution_and_concatenation_commute.
              destruct (IHae2 (n1 :: ds)) as [IHae2_nat IHae2_s].
              rewrite -> (IHae2_nat n2 eq_refl).
              rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
              unfold decode_execute.
              rewrite -> n1_n2.
              remember "numerical underflow: -"%string as msg eqn:H_msg.
              injection H_eval_s as H_eval_s.
              rewrite -> H_eval_s.
              reflexivity.
           ++ discriminate.
        -- rewrite -> fold_unfold_compile_aux_Minus.
           rewrite -> execution_and_concatenation_commute.
           destruct (IHae1 ds) as [IHae1_nat IHae1_s].
           rewrite -> (IHae1_nat n1 eq_refl).
           rewrite -> execution_and_concatenation_commute.
           destruct (IHae2 (n1 :: ds)) as [IHae2_nat IHae2_s].
           rewrite -> (IHae2_s s H_eval_s).
           reflexivity.
      * rewrite -> fold_unfold_compile_aux_Minus.
        rewrite -> execution_and_concatenation_commute.
        destruct (IHae1 ds) as [IHae1_nat IHae1_s].
        rewrite -> (IHae1_s s1 eq_refl).
        injection H_eval_s as H_eval_s.
        rewrite -> H_eval_s.
        reflexivity.
Qed.

Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).
 Proof.
   intro sp.
   destruct sp as [ae].
   unfold interpret, compile, run.
   destruct (about_evaluate_outputs ae nil) as [H_nat H_s].
   case (evaluate ae) as [n | s].
   + rewrite -> (H_nat n eq_refl).
     reflexivity.
   + rewrite -> (H_s s eq_refl).
     reflexivity.    
 Qed.

(* ********** *)

(* Byte-code verification:
   the following verifier symbolically executes a byte-code program
   to check whether no underflow occurs during execution
   and whether when the program completes,
   there is one and one only natural number on top of the stack.
   The second argument of verify_aux is a natural number
   that represents the size of the stack.
*)

Fixpoint verify_aux (bcis : list byte_code_instruction) (n : nat) : option nat :=
  match bcis with
    | nil =>
      Some n
    | bci :: bcis' =>
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end
  end.

Lemma fold_unfold_verify_aux_nil:
  forall (n : nat),
    verify_aux nil n = Some n.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons:
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (n: nat),
    verify_aux (bci :: bcis') n = match bci with
                                  | PUSH _ =>
                                    verify_aux bcis' (S n)
                                  | _ =>
                                    match n with
                                    | S (S n') =>
                                      verify_aux bcis' (S n')
                                    | _ =>
                                      None
                                    end
                                  end.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Definition verify (p : target_program) : bool :=
  match p with
  | Target_program bcis =>
    match verify_aux bcis 0 with
    | Some n =>
      match n with
      | 1 =>
        true
      | _ =>
        false
      end
    | _ =>
      false
    end
  end.

(* Task 10 (time permitting):
   Prove that the compiler emits code
   that is accepted by the verifier.
 *)

(*
Lemma about_verifying :
  forall (ae : arithmetic_expression)
         (bcis : list byte_code_instruction)
         (n : nat),
    verify_aux ((compile_aux ae) ++ bcis) n =
    match verify_aux (compile_aux ae) 0 with
    | Some 1 => verify_aux bcis (S n)
    | _ => None
    end.
Proof.
  intros ae.
  induction ae as [n' | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - intros bcis n.
    rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> app_nil_l.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
  - intros bcis n.
    rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> app_assoc_reverse.
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_append_nil.
    Check (IHae1 (compile_aux ae2 ++ ADD :: bcis) n).
    rewrite -> (IHae1 (compile_aux ae2 ++ ADD :: bcis) n).
    rewrite -> (IHae1 (compile_aux ae2 ++ ADD :: nil) 0).
    case (verify_aux (compile_aux ae1) 0) eqn: H_ver_ae1.
    * case n0 as [ | n0'].
      -- reflexivity.
      -- case n0' as [ | n0''].
         ++ rewrite -> (IHae2 (ADD :: bcis) (S n)).
            rewrite -> (IHae2 (ADD :: nil) 1).
            case (verify_aux (compile_aux ae2) 0) eqn: H_ver_ae2.
            ** case n0 as [ | n0'].
               --- reflexivity.
               --- case n0' as [ | n0''].
                   +++ rewrite -> fold_unfold_verify_aux_cons.
                       rewrite -> fold_unfold_verify_aux_cons.
                       rewrite -> fold_unfold_verify_aux_nil.
                       reflexivity.
                   +++ reflexivity.
            ** reflexivity.
         ++ reflexivity.
    * reflexivity.
  - intros bcis n.
    rewrite -> fold_unfold_compile_aux_Minus.
    rewrite -> app_assoc_reverse.
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_append_nil.
    Check (IHae1 (compile_aux ae2 ++ SUB :: bcis) n).
    rewrite -> (IHae1 (compile_aux ae2 ++ SUB :: bcis) n).
    rewrite -> (IHae1 (compile_aux ae2 ++ SUB :: nil) 0).
    case (verify_aux (compile_aux ae1) 0) eqn: H_ver_ae1.
    * case n0 as [ | n0'].
      -- reflexivity.
      -- case n0' as [ | n0''].
         ++ rewrite -> (IHae2 (SUB :: bcis) (S n)).
            rewrite -> (IHae2 (SUB :: nil) 1).
            case (verify_aux (compile_aux ae2) 0) eqn: H_ver_ae2.
            ** case n0 as [ | n0'].
               --- reflexivity.
               --- case n0' as [ | n0''].
                   +++ rewrite -> fold_unfold_verify_aux_cons.
                       rewrite -> fold_unfold_verify_aux_cons.
                       rewrite -> fold_unfold_verify_aux_nil.
                       reflexivity.
                   +++ reflexivity.
            ** reflexivity.
         ++ reflexivity.
    * reflexivity.
Qed.
*)

(* but we know that verify_aux (compile_aux ae) 0 always evaluates to Some 1,
   so we don't need to consider any other cases *)

Lemma about_verifying :
  forall (ae : arithmetic_expression)
         (bcis : list byte_code_instruction)
         (n : nat),
    verify_aux ((compile_aux ae) ++ bcis) n =
    verify_aux bcis (S n).
Proof.
  intro ae.
  induction ae as [k | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
  - intros bcis n.
    rewrite -> (fold_unfold_compile_aux_Literal k).
    rewrite -> (fold_unfold_append_cons (PUSH k) nil bcis).
    rewrite -> (fold_unfold_append_nil bcis).
    exact (fold_unfold_verify_aux_cons (PUSH k) bcis n).
 - intros bcis n.
   rewrite -> (fold_unfold_compile_aux_Plus ae1 ae2).
   rewrite <- (app_assoc (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) bcis).
   rewrite <- (app_assoc (compile_aux ae2) (ADD :: nil) bcis).
   rewrite -> (fold_unfold_append_cons (ADD) nil bcis).
   rewrite -> (fold_unfold_append_nil bcis).
   rewrite -> (IHae1 (compile_aux ae2 ++ ADD :: bcis) n).
   rewrite -> (IHae2 (ADD :: bcis) (S n)).

   exact (fold_unfold_verify_aux_cons ADD bcis (S (S n))).
 - intros bcis n.
   rewrite -> (fold_unfold_compile_aux_Minus ae1 ae2).
   rewrite <- (app_assoc (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) bcis).
   rewrite <- (app_assoc (compile_aux ae2) (SUB :: nil) bcis).
   rewrite -> (fold_unfold_append_cons SUB nil bcis).
   rewrite -> (fold_unfold_append_nil bcis).
   rewrite -> (IHae1 (compile_aux ae2 ++ SUB :: bcis) n).
   rewrite -> (IHae2 (SUB :: bcis) (S n)).
   exact (fold_unfold_verify_aux_cons SUB bcis (S (S n))).
Qed.

(* auxiliary lemma for auxiliary function *)

Lemma compiler_aux_emits_well_behaved_code :
  forall ae : arithmetic_expression,
    verify_aux (compile_aux ae) 0 = Some 1.
Proof.
  intro ae.
  destruct ae as [n | ae1 ae2 | ae1 ae2].
  - reflexivity.
  - rewrite -> (fold_unfold_compile_aux_Plus ae1 ae2).
    rewrite -> (about_verifying ae1 (compile_aux ae2 ++ ADD :: nil) 0).
    rewrite -> (about_verifying ae2 (ADD :: nil) 1).
    reflexivity.
  - rewrite -> (fold_unfold_compile_aux_Minus ae1 ae2).
    rewrite -> (about_verifying ae1 (compile_aux ae2 ++ SUB :: nil) 0).
    rewrite -> (about_verifying ae2 (SUB :: nil) 1).
    reflexivity.
Qed.

Theorem the_compiler_emits_well_behaved_code :
  forall ae : arithmetic_expression,
    verify (compile (Source_program ae)) = true.
Proof.
  intro ae.
  unfold verify, compile.
  rewrite -> (compiler_aux_emits_well_behaved_code ae).
  reflexivity.
Qed.

(* Subsidiary question:
   What is the practical consequence of this theorem?
*)

(* ********** *)

(* Task 11 *)
(* a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.*)


Inductive Nat : Type :=
| O : Nat
| S : Nat -> Nat.

(* Arithmetic expressions: *)

Inductive arithmetic_expression' : Type :=
| Literal' : Nat -> arithmetic_expression'
| Plus' : arithmetic_expression' -> arithmetic_expression' -> arithmetic_expression'
| Minus' : arithmetic_expression' -> arithmetic_expression' -> arithmetic_expression'.

(* Source programs: *)

 Inductive source_program' : Type :=
 | Source_program' : arithmetic_expression' -> source_program'.

 (* Semantics: *)

Inductive expressible_value' : Type :=
| Expressible_nat' : Nat -> expressible_value'
| Expressible_msg' : string -> expressible_value'.

Fixpoint evaluate' (ae: arithmetic_expression') : expressible_value' :=
  match ae with
  | Literal' n =>
    Expressible_nat' n
  | Plus' ae1 ae2  =>
    match evaluate' ae1 with
    | Expressible_msg' s1 => Expressible_msg' s1
    | Expressible_nat' n1 => match evaluate' ae2 with
                            | Expressible_msg' s2 => Expressible_msg' s2
                            | Expressible_nat' n2 => Expressible_nat' (n1 + n2)
                            end
    end
  | Minus' ae1 ae2  =>
    match evaluate' ae1 with
    | Expressible_msg' s1 => Expressible_msg' s1
    | Expressible_nat' n1 => match evaluate' ae2 with
                            | Expressible_msg' s2 => Expressible_msg' s2
                            | Expressible_nat' n2 =>
                              if n1 <? n2
                              then Expressible_msg'
                                     (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
                              else Expressible_nat' (n1 - n2)
                            end
    end
  end.



(*
   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.

   d. Prove that the Magritte target interpreter is (essentially)
      a left inverse of the compiler, i.e., it is a decompiler.
*)

(* ********** *)

(* end of term-project.v *)
