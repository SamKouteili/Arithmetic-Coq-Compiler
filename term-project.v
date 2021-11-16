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

Fixpoint evaluate_cps (ae : arithmetic_expression)
         (k : nat -> expressible_value) : expressible_value :=
  match ae with
  | Literal n =>
    k n
  | Plus ae1 ae2 =>
    evaluate_cps ae1 (fun n1 =>
                        evaluate_cps ae2 (fun n2 => k (n1 + n2)))
  | Minus ae1 ae2 =>
     evaluate_cps ae1 (fun n1 =>
                         evaluate_cps ae2
                                      (fun n2 =>
                                         match n1 <? n2 with
                                         | true =>
                                           Expressible_msg
                                             (String.append "numerical underflow: -"
                                                            (string_of_nat (n2 - n1)))
                                         | false =>
                                           k (n1 - n2)
                                         end))
  end.

Definition evaluate (ae : arithmetic_expression) :=
  evaluate_cps ae (fun n => Expressible_nat n).

Compute (evaluate (Plus (Plus (Literal 1) (Literal 2)) (Literal 2 ))).
Compute (evaluate (Minus (Literal 1) (Literal 2))).


Lemma fold_unfold_evaluate_cps_Literal :
  forall (n : nat) (k : nat -> expressible_value),
    evaluate_cps (Literal n) k = k n.
Proof.
  fold_unfold_tactic evaluate_cps.
Qed.

Lemma fold_unfold_evaluate_cps_Plus :
  forall (ae1 ae2 : arithmetic_expression) (k : nat -> expressible_value),
    evaluate_cps (Plus ae1 ae2) k =
    evaluate_cps ae1 (fun n1 =>
                        evaluate_cps ae2 (fun n2 => k (n1 + n2))).
Proof.
  fold_unfold_tactic evaluate_cps.
Qed.

Lemma fold_unfold_evaluate_cps_Minus :
  forall (ae1 ae2 : arithmetic_expression) (k : nat -> expressible_value),
    evaluate_cps (Minus ae1 ae2) k =
    evaluate_cps ae1 (fun n1 =>
                        evaluate_cps ae2 (fun n2 =>
                                            match n1 <? n2 with
                                            | true =>
                                              Expressible_msg
                                                (String.append "numerical underflow: -"
                                                               (string_of_nat (n2 - n1)))
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
  induction ae as [n
                  | ae1 [[n1  [IHae1 IHae1_cps]] | [s1 [IHae1 IHae1_cps]]]
                        ae2 [[n2  [IHae2 IHae2_cps]] | [s2  [IHae2 IHae2_cps]]]
                  | ae1 [[n1  [IHae1 IHae1_cps]] | [s1 [IHae1 IHae1_cps]]]
                        ae2 [[n2  [IHae2 IHae2_cps]] | [s2  [IHae2 IHae2_cps]]]];
    unfold specification_of_evaluate in S_evaluate.
  (* ae is Literal *)
  + left.
    destruct S_evaluate as [S_Literal _].
    exists n.
    split.
    ++ exact (S_Literal n).
    ++ intro k.
       rewrite -> fold_unfold_evaluate_cps_Literal.
       reflexivity.
    (* ae is Plus *)
  + left.
    destruct S_evaluate as [_ [[_ [_ S_Plus_n1n2]] _]].
    Check (S_Plus_n1n2 ae1 ae2 n1 n2 IHae1 IHae2).
    exists (n1 + n2).
    split.
    ++ exact (S_Plus_n1n2 ae1 ae2 n1 n2 IHae1 IHae2).
    ++ intro k.
       rewrite -> fold_unfold_evaluate_cps_Plus.
       Check (IHae1_cps (fun n0 : nat =>
                           evaluate_cps ae2 (fun n3 : nat => k (n0 + n3)))).
       rewrite -> (IHae1_cps (fun n0 : nat =>
                                evaluate_cps ae2 (fun n3 : nat => k (n0 + n3)))).
       rewrite -> (IHae2_cps (fun n0 : nat => k (n1 + n0))).
       reflexivity.
  + right.
    destruct S_evaluate as [_ [[_ [S_Plus_n1_s2 _]] _]].
    Check (S_Plus_n1_s2 ae1 ae2 n1 s2 IHae1 IHae2).
    exists s2.
    split.
    ++ exact (S_Plus_n1_s2 ae1 ae2 n1 s2 IHae1 IHae2).
    ++ intro k.
       rewrite -> fold_unfold_evaluate_cps_Plus.
       rewrite -> (IHae1_cps (fun n0 : nat =>
                               evaluate_cps ae2 (fun n2 : nat => k (n0 + n2)))).
       rewrite -> (IHae2_cps (fun n2 : nat => k (n1 + n2))).
       reflexivity.
  + right.
    destruct S_evaluate as [_ [[S_Plus_s1_n2 [_ _]] _]].
    exists s1.
    split.
    ++ exact (S_Plus_s1_n2 ae1 ae2 s1 IHae1).
    ++ intro k.
       rewrite -> fold_unfold_evaluate_cps_Plus.
       rewrite -> IHae1_cps.
       reflexivity.
  + right.
    exists s1.
    destruct S_evaluate as [_ [[S_Plus_s1_n2 [_ _]] _]].
    split.
    ++ exact (S_Plus_s1_n2 ae1 ae2 s1 IHae1).
    ++ intro k.
       rewrite -> fold_unfold_evaluate_cps_Plus.
       rewrite -> (IHae1_cps
                     (fun n1 : nat =>
                        evaluate_cps ae2 (fun n2 : nat => k (n1 + n2)))).
       reflexivity.
   (* ae is Minus *)
  + case (n1 <? n2) eqn:H_n1_n2.
    ++ right.
       destruct S_evaluate as [_ [_ [_ [_ [S_Minus_n1_n2_msg _]]]]].
       Check (S_Minus_n1_n2_msg ae1 ae2 n1 n2 IHae1 IHae2 H_n1_n2).
       exists (String.append
                 "numerical underflow: -" (string_of_nat (n2 - n1))).
       split.
       +++ exact (S_Minus_n1_n2_msg ae1 ae2 n1 n2 IHae1 IHae2 H_n1_n2).
       +++ intro k.
           rewrite -> fold_unfold_evaluate_cps_Minus.
           rewrite -> IHae1_cps.
           rewrite -> IHae2_cps.
           rewrite -> H_n1_n2.
           reflexivity.
    ++ left.
       destruct S_evaluate as [_ [_ [_ [_ [_ S_Minus_n1_n2_nat]]]]].
       Check (S_Minus_n1_n2_nat ae1 ae2 n1 n2 IHae1 IHae2 H_n1_n2).
       exists (n1 - n2).
       split.
       +++ exact (S_Minus_n1_n2_nat ae1 ae2 n1 n2 IHae1 IHae2 H_n1_n2).
       +++ intro k.
           rewrite -> fold_unfold_evaluate_cps_Minus.
           rewrite -> IHae1_cps.
           rewrite -> IHae2_cps.
           rewrite -> H_n1_n2.
           reflexivity.
  + right.
    destruct S_evaluate as [_ [_ [_ [S_Minus_n1_s2 _]]]].
    Check (S_Minus_n1_s2 ae1 ae2 n1 s2 IHae1 IHae2).
    exists s2.
    split.
    ++ exact (S_Minus_n1_s2 ae1 ae2 n1 s2 IHae1 IHae2).
    ++ intro k.
       rewrite -> fold_unfold_evaluate_cps_Minus.
       rewrite -> IHae1_cps.
       rewrite -> IHae2_cps.
       reflexivity.
  + right.
    destruct S_evaluate as [_ [_ [S_Minus_s1_n2 _]]].
    Check (S_Minus_s1_n2 ae1 ae2 s1 IHae1).
    exists s1.
    split.
    ++ exact (S_Minus_s1_n2 ae1 ae2 s1 IHae1).
    ++ intro k.
       rewrite -> fold_unfold_evaluate_cps_Minus.
       rewrite -> IHae1_cps.
       reflexivity.
  + right.
    destruct S_evaluate as [_ [_ [S_Minus_s1_n2 _]]].
    Check (S_Minus_s1_n2 ae1 ae2 s1 IHae1).
    exists s1.
    split.
    ++ exact (S_Minus_s1_n2 ae1 ae2 s1 IHae1).
    ++ intro k.
       rewrite -> fold_unfold_evaluate_cps_Minus.
       rewrite -> IHae1_cps.
       reflexivity.
Qed.


(* probably wrong way to go about it *)
Theorem evaluate_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate.
Proof.
  unfold evaluate, specification_of_evaluate.
  split.
  + intro n.
    rewrite -> fold_unfold_evaluate_cps_Literal.
    reflexivity.
  + split; split.
    ++ intros ae1 ae2 s1 IHae.
       rewrite -> fold_unfold_evaluate_cps_Plus.
       Admitted.
           
          

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
  Check (about_evaluate_cps evaluate S_evaluate ae).
  destruct (about_evaluate_cps evaluate S_evaluate ae)
    as [[n [H_eval H_eval_cps]] | [s [H_eval H_eval_cps]]];
    unfold interpret;
    rewrite (H_eval_cps (fun n => Expressible_nat n));
    exact (eq_sym H_eval).
Qed.


(*
Theorem there_exists_at_most_one_evaluate_function :
  forall (ev1 ev2 : arithmetic_expression -> expressible_value),
    specification_of_evaluate ev1 ->
    specification_of_evaluate ev2 ->
    forall (ae : arithmetic_expression),
      ev1 ae = ev2 ae.
Proof.
  intros ev1 ev2 ev1_spec ev2_spec ae.
  case ae.
  + intro n.
    destruct ev1_spec as [ev1_spec_literal _].
    destruct ev2_spec as [ev2_spec_literal _].
    rewrite -> ev2_spec_literal.
    exact (ev1_spec_literal n).
  + intros ae1 ae2.
    destruct ev1_spec.
    
  destruct ev1_spec.

Started but realized it was the least important on the list 
*)

  
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

(*
Definition decode_execute (bcis : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  ...

Theorem decode_execute_satisfies_the_specification_of_decode_execute :
  specification_of_decode_execute decode_execute.
Proof.
Abort.
*)

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
