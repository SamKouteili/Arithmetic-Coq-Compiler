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

Fixpoint evaluate_cps (ae : arithmetic_expression) (k : nat -> expressible_value) : expressible_value :=
  match ae with
  | Literal n =>
    k n
  | Plus ae1 ae2 =>
    evaluate_cps ae1 (fun n1 =>
                        evaluate_cps ae2 (fun n2 =>
                                            k (n1 + n2)))
  | Minus ae1 ae2 =>
    evaluate_cps ae1 (fun n1 =>
                        evaluate_cps ae2 (fun n2 =>
                                            match n1 <? n2 with
                                            | true =>
                                              Expressible_msg
                                                (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
                                            | false =>
                                              k (n1 - n2)
                                            end))
  end.

Lemma fold_unfold_evaluate_cps_Literal :
  forall (n : nat)
         (k : nat -> expressible_value),
    evaluate_cps (Literal n) k =
    k n.
Proof.
  fold_unfold_tactic evaluate_cps.
Qed.

Lemma fold_unfold_evaluate_cps_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (k : nat -> expressible_value),
    evaluate_cps (Plus ae1 ae2) k =
    evaluate_cps ae1 (fun n1 =>
                        evaluate_cps ae2 (fun n2 =>
                                            k (n1 + n2))).
Proof.
  fold_unfold_tactic evaluate_cps.
Qed.

Lemma fold_unfold_evaluate_cps_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (k : nat -> expressible_value),
    evaluate_cps (Minus ae1 ae2) k =
    evaluate_cps ae1 (fun n1 =>
                        evaluate_cps ae2 (fun n2 =>
                                            match n1 <? n2 with
                                            | true =>
                                              Expressible_msg
                                                (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
                                            | false =>
                                              k (n1 - n2)
                                            end)).
Proof.
  fold_unfold_tactic evaluate_cps.
Qed.

Lemma about_evaluate_cps :
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      (exists n : nat,
          evaluate ae = Expressible_nat n
          /\
          forall k : nat -> expressible_value,
            evaluate_cps ae k = k n)
      \/
      (exists s : string,
          evaluate ae = Expressible_msg s
          /\
          forall k : nat -> expressible_value,
            evaluate_cps ae k = Expressible_msg s).
Proof.
  intros evaluate S_evaluate ae.
  induction ae as [n |
                   ae1 [[n1 [IHae1 IHae1_cps]] | [s1 [IHae1 IHae1_cps]]] ae2 [[n2 [IHae2 IHae2_cps]] | [s2 [IHae2 IHae2_cps]]] |
                   ae1 [[n1 [IHae1 IHae1_cps]] | [s1 [IHae1 IHae1_cps]]] ae2 [[n2 [IHae2 IHae2_cps]] | [s2 [IHae2 IHae2_cps]]]].
  - unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [S_Literal _].
    left.
    exists n.
    split.
    + exact (S_Literal n).
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Literal.
      reflexivity.
  - unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [[_ [_ S_Plus_n1_n2]] _]].
    Check (S_Plus_n1_n2
             ae1
             ae2
             n1
             n2
             IHae1
             IHae2).
    left.
    exists (n1 + n2).
    split.
    + exact (S_Plus_n1_n2
             ae1
             ae2
             n1
             n2
             IHae1
             IHae2).
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Plus.
      Check (IHae1_cps (fun n0 : nat => evaluate_cps ae2 (fun n3 : nat => k (n0 + n3)))).
      rewrite -> (IHae1_cps (fun n0 : nat => evaluate_cps ae2 (fun n3 : nat => k (n0 + n3)))).
      rewrite -> (IHae2_cps (fun n3 : nat => k (n1 + n3))).
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [[_ [S_Plus_n1_s2 _]] _]].
    Check (S_Plus_n1_s2
             ae1
             ae2
             n1
             s2
             IHae1
             IHae2).
    exists s2.
    split.
    + exact (S_Plus_n1_s2
             ae1
             ae2
             n1
             s2
             IHae1
             IHae2).
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Plus.
      rewrite -> (IHae1_cps (fun n0 : nat => evaluate_cps ae2 (fun n2 : nat => k (n0 + n2)))).
      rewrite -> (IHae2_cps (fun n2 : nat => k (n1 + n2))).
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [[S_Plus_s1_n2 [_ _]] _]].
    Check (S_Plus_s1_n2
             ae1
             ae2
             s1
             IHae1).
    exists s1.
    split.
    + exact (S_Plus_s1_n2
             ae1
             ae2
             s1
             IHae1).
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Plus.
      rewrite -> (IHae1_cps (fun n1 : nat => evaluate_cps ae2 (fun n0 : nat => k (n1 + n0)))).
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [[S_Plus_s1_n2 [_ _]] _]].
    exists s1.
    Check (S_Plus_s1_n2 ae1 ae2 s1 IHae1).
    split.
    + exact (S_Plus_s1_n2 ae1 ae2 s1 IHae1).
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Plus.
      rewrite -> (IHae1_cps (fun n1 : nat => evaluate_cps ae2 (fun n2 : nat => k (n1 + n2)))).
      reflexivity.
  - case (n1 <? n2) eqn:H_n1_n2.
    + right.
      unfold specification_of_evaluate in S_evaluate.
      destruct S_evaluate as [_ [_ [_ [_ [S_Minus_n1_n2_msg _]]]]].
      Check (S_Minus_n1_n2_msg ae1 ae2 n1 n2 IHae1 IHae2 H_n1_n2).
      exists (String.append "numerical underflow: -" (string_of_nat (n2 - n1))).
      split.
      * exact (S_Minus_n1_n2_msg ae1 ae2 n1 n2 IHae1 IHae2 H_n1_n2).
      * intro k.
        rewrite -> fold_unfold_evaluate_cps_Minus.
        rewrite -> (IHae1_cps (fun n0 : nat =>
                                 evaluate_cps ae2
                                              (fun n3 : nat =>
                                                 if n0 <? n3
                                                 then
                                                   Expressible_msg
                                                     ("numerical underflow: -" ++ string_of_nat (n3 - n0))
                                                 else k (n0 - n3)))).
        rewrite -> (IHae2_cps (fun n3 : nat =>
                                 if n1 <? n3
                                 then
                                   Expressible_msg ("numerical underflow: -" ++ string_of_nat (n3 - n1))
                                 else k (n1 - n3))).
        rewrite -> H_n1_n2.
        reflexivity.
    + left.
      unfold specification_of_evaluate in S_evaluate.
      destruct S_evaluate as [_ [_ [_ [_ [_ S_Minus_n1_n2_nat]]]]].
      Check (S_Minus_n1_n2_nat ae1 ae2 n1 n2 IHae1 IHae2 H_n1_n2).
      exists (n1 - n2).
      split.
      * exact (S_Minus_n1_n2_nat ae1 ae2 n1 n2 IHae1 IHae2 H_n1_n2).
      * intro k.
        rewrite -> fold_unfold_evaluate_cps_Minus.
        rewrite -> (IHae1_cps (fun n0 : nat =>
                                 evaluate_cps ae2
                                              (fun n3 : nat =>
                                                 if n0 <? n3
                                                 then
                                                   Expressible_msg
                                                     ("numerical underflow: -" ++ string_of_nat (n3 - n0))
                                                 else k (n0 - n3)))).
        rewrite -> (IHae2_cps (fun n3 : nat =>
                                 if n1 <? n3
                                 then
                                   Expressible_msg ("numerical underflow: -" ++ string_of_nat (n3 - n1))
                                 else k (n1 - n3))).
        rewrite -> H_n1_n2.
        reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [_ [_ [S_Minus_n1_s2 _]]]].
    Check (S_Minus_n1_s2
             ae1
             ae2
             n1
             s2
             IHae1
             IHae2).
    exists s2.
    split.
    + exact (S_Minus_n1_s2
             ae1
             ae2
             n1
             s2
             IHae1
             IHae2).
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Minus.
      rewrite -> (IHae1_cps (fun n0 : nat =>
                               evaluate_cps ae2
                                            (fun n2 : nat =>
                                               if n0 <? n2
                                               then
                                                 Expressible_msg
                                                   ("numerical underflow: -" ++ string_of_nat (n2 - n0))
                                               else k (n0 - n2)))).
      rewrite -> (IHae2_cps (fun n2 : nat =>
                               if n1 <? n2
                               then
                                 Expressible_msg ("numerical underflow: -" ++ string_of_nat (n2 - n1))
                               else k (n1 - n2))).
      reflexivity.
  - unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [_ [S_Minus_s1_n2 [_ _]]]].
    Check (S_Minus_s1_n2 ae1 ae2 s1 IHae1).
    right.
    exists s1.
    split.
    + exact (S_Minus_s1_n2 ae1 ae2 s1 IHae1).
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Minus.
      rewrite -> (IHae1_cps (fun n1 : nat =>
                               evaluate_cps ae2
                                            (fun n0 : nat =>
                                               if n1 <? n0
                                               then
                                                 Expressible_msg
                                                   ("numerical underflow: -" ++ string_of_nat (n0 - n1))
                                               else k (n1 - n0)))).
      reflexivity.
  - right.
    unfold specification_of_evaluate in S_evaluate.
    destruct S_evaluate as [_ [_ [S_Minus_s1_n2 [_ _]]]].
    exists s1.
    Check (S_Minus_s1_n2 ae1 ae2 s1 IHae1).
    split.
    + exact (S_Minus_s1_n2 ae1 ae2 s1 IHae1).
    + intro k.
      rewrite -> fold_unfold_evaluate_cps_Minus.
      rewrite -> (IHae1_cps (fun n1 : nat =>
                               evaluate_cps ae2
                                            (fun n2 : nat =>
                                               if n1 <? n2
                                               then
                                                 Expressible_msg
                                                   ("numerical underflow: -" ++ string_of_nat (n2 - n1))
                                               else k (n1 - n2)))).
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
  unfold specification_of_evaluate.
  repeat split; intros ae1 ae2; (rewrite -> (fold_unfold_evaluate_Literal) || rewrite -> (fold_unfold_evaluate_Plus) || rewrite -> (fold_unfold_evaluate_Minus)).
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

    Restart.
    unfold specification_of_evaluate.
    repeat split;
      intros ae1 ae2;
      (rewrite -> (fold_unfold_evaluate_Literal) ||
       rewrite -> (fold_unfold_evaluate_Plus) ||
       rewrite -> (fold_unfold_evaluate_Minus));
      ((intros s1 H_evaluate_ae1; rewrite -> H_evaluate_ae1; reflexivity) ||
       (intros n1 n2 H_evaluate_ae1 H_evaluate_ae2; rewrite -> H_evaluate_ae1; rewrite -> H_evaluate_ae2;  reflexivity) ||
       (intros n1 n2 H_evaluate_ae1 H_evaluate_ae2 H_lesser_than; rewrite -> H_evaluate_ae1; rewrite -> H_evaluate_ae2; rewrite -> H_lesser_than; reflexivity)).
    Qed.

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae =>
    evaluate_cps ae (fun (n : nat) => Expressible_nat n)
  end.

Theorem interpret_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret.
  intros evaluate S_evaluate ae.
  Check (about_evaluate_cps
           evaluate
           S_evaluate
           ae).
  destruct (about_evaluate_cps
              evaluate
              S_evaluate
              ae) as [[n [H_eval H_eval_cps]] | [s [H_eval H_eval_cps]]].
  - unfold interpret.
    Check (H_eval_cps (fun n => Expressible_nat n)).
    rewrite -> (H_eval_cps (fun n => Expressible_nat n)).
    Check (eq_sym H_eval).
    exact (eq_sym H_eval).
  - unfold interpret.
    Check (H_eval_cps (fun n => Expressible_nat n)).
    rewrite -> (H_eval_cps (fun n => Expressible_nat n)).
    exact (eq_sym H_eval).
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
  destruct bcis.
  - unfold specification_of_decode_execute in S_decode_execute_1.
    destruct S_decode_execute_1 as [S_PUSH_1 _].
    unfold specification_of_decode_execute in S_decode_execute_2.
    destruct S_decode_execute_2 as [S_PUSH_2 _].
    rewrite -> (S_PUSH_2 n ds).
    exact (S_PUSH_1 n ds).
  - unfold specification_of_decode_execute in S_decode_execute_1.
    destruct S_decode_execute_1 as [ _ [[S_ADD_nil_1 [S_ADD_cons_1 S_ADD_cons_cons_1]] _]].
    destruct S_decode_execute_2 as [ _ [[S_ADD_nil_2 [S_ADD_cons_2 S_ADD_cons_cons_2]] _]].
    destruct ds as [ | n1].
    -- rewrite -> S_ADD_nil_2.
       exact (S_ADD_nil_1).
    -- destruct ds as [ | n2].
       --- rewrite -> (S_ADD_cons_2 n1).
           exact (S_ADD_cons_1 n1).
       --- rewrite -> (S_ADD_cons_cons_2 n2 n1 ds).
           exact (S_ADD_cons_cons_1 n2 n1 ds).
 - unfold specification_of_decode_execute in S_decode_execute_1.
    destruct S_decode_execute_1 as [ _ [_ [S_SUB_nil_1 [S_SUB_cons_1 [S_SUB_cons_cons_lesser_than_1 S_SUB_cons_cons_not_lesser_than_1]]]]].
    destruct S_decode_execute_2 as [ _ [_ [S_SUB_nil_2 [S_SUB_cons_2 [S_SUB_cons_cons_lesser_than_2 S_SUB_cons_cons_not_lesser_than_2]]]]].
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
  unfold specification_of_decode_execute.
  repeat split; (* since there are 7 conjunctions, I thought this would result in 8 subgoals
                   but it only gives two... *)
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

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
    match bcis with
      | nil => OK ds
      | bci :: bcis' => match decode_execute bci ds with
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
    fetch_decode_execute_loop (bci :: bcis') ds = match decode_execute bci ds with
                                                  | OK ds' => fetch_decode_execute_loop bcis' ds'
                                                  | KO s => KO s
                                                  end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Theorem there_is_at_most_one_fetch_decode_execute_loop :
  forall (fetch_decode_execute_loop_1 fetch_decode_execute_loop_2 :list byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_1 ->
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_2 ->
    forall (bcis : list  byte_code_instruction)
           (ds : data_stack),
      fetch_decode_execute_loop_1 bcis ds = fetch_decode_execute_loop_2 bcis ds.
Proof.
  intros fetch_decode_execute_loop_1 fetch_decode_execute_loop_2
         S_fetch_decode_execute_loop_1
         S_fetch_decode_execute_loop_2
         bcis.
  unfold specification_of_fetch_decode_execute_loop in S_fetch_decode_execute_loop_1.
  assert (S_fetch_decode_execute_loop_1 :=
            S_fetch_decode_execute_loop_1
              decode_execute
              decode_execute_satisfies_the_specification_of_decode_execute).
  unfold specification_of_fetch_decode_execute_loop in S_fetch_decode_execute_loop_2.
  assert (S_fetch_decode_execute_loop_2 :=
            S_fetch_decode_execute_loop_2
              decode_execute
              decode_execute_satisfies_the_specification_of_decode_execute).
  induction bcis as [ | bci bcis' IHbcis'].
  - intro ds.
    destruct S_fetch_decode_execute_loop_1 as [H_nil_1 _].
    destruct S_fetch_decode_execute_loop_2 as [H_nil_2 _].
    rewrite -> (H_nil_2 ds).
    exact (H_nil_1 ds).
  - intro ds.
    destruct (decode_execute bci ds) as [ds' | s] eqn: H_decode_execute.
    -- destruct S_fetch_decode_execute_loop_1 as [_ [H_decode_execute_OK_1 _]].
       destruct S_fetch_decode_execute_loop_2 as [_ [H_decode_execute_OK_2 _]].
       rewrite -> (H_decode_execute_OK_1 bci bcis' ds ds' H_decode_execute).
       rewrite -> (H_decode_execute_OK_2 bci bcis' ds ds' H_decode_execute).
       exact (IHbcis' ds').
    -- destruct S_fetch_decode_execute_loop_1 as [_ [_ H_decode_execute_KO_1]].
       destruct S_fetch_decode_execute_loop_2 as [_ [_ H_decode_execute_KO_2]].
       rewrite -> (H_decode_execute_KO_2 bci bcis' ds s H_decode_execute).
       exact (H_decode_execute_KO_1 bci bcis' ds s H_decode_execute).
Qed.

Theorem fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute0 H_decode_execute0_satisfies_the_specification_of_decode_execute.
  repeat split; intros bci bcis' ds. 
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
   destruct (decode_execute bci1 ds) as [ds' | ds'].
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

Definition run (t : target_program) : expressible_value :=
  match t with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
    | KO s => Expressible_msg s
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
  intros fetch_decode_execute_loop0 S_fetch_decode_execute_loop0.
  repeat split;
    intro bcis;
    rewrite -> (there_is_at_most_one_fetch_decode_execute_loop
                  fetch_decode_execute_loop0 
                  fetch_decode_execute_loop
                  S_fetch_decode_execute_loop0
                  fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop).
  - intro H_fetch_decode_execute_loop.
    unfold run.
    rewrite -> H_fetch_decode_execute_loop.
    reflexivity.
  - intros n H_fetch_decode_execute_loop.
    unfold run.
    rewrite -> H_fetch_decode_execute_loop.
    reflexivity.
  - intros n n' ds'' H_fetch_decode_execute_loop.
    unfold run.
    rewrite -> H_fetch_decode_execute_loop.
    reflexivity.
 - intros s H_fetch_decode_execute_loop.
    unfold run.
    rewrite -> H_fetch_decode_execute_loop.
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

(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
*)

(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
*)

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
Theorem the_compiler_emits_well_behaved_code :
  forall ae : arithmetic_expression,
    verify (compile ae) = true.
Proof.
Abort.
*)

(* Subsidiary question:
   What is the practical consequence of this theorem?
*)

(* ********** *)

(* Task 11:

   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

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
