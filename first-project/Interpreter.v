From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Import ListNotations.
From FirstProject Require Import Imp Maps.


Inductive interpreter_result : Type :=
  | Success (s: state * (list (state*com)))
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)


Notation "'LETOPT' '(' x ',' y ')' <== e1 'IN' e2"
  := (match e1 with
          | Success (x, y) => e2
          | Fail => Fail
          | OutOfGas => OutOfGas
       end)
(right associativity, at level 60).

(**
  2.1. DONE: Implement ceval_step as specified. To improve readability,
             you are strongly encouraged to define auxiliary notation.
             See the notation LETOPT in the ImpCEval chapter.
*)

Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  match i with
  | 0 => OutOfGas
  | S n => match c with
           | <{ skip }> => Success (st, continuation)
           | <{ X := a }> => Success (X !-> (aeval st a); st, continuation)
           | <{ c1; c2 }> => LETOPT (st', continuation') <== ceval_step st c1 continuation n
                             IN ceval_step st' c2 continuation' n
           | <{ if b then c1 else c2 end }> => if beval st b
                                               then ceval_step st c1 continuation n
                                               else ceval_step st c2 continuation n
           | <{ while b do c1 end }> => if beval st b
                                        then LETOPT (st', continuation') <== ceval_step st c1 continuation n
                                             IN ceval_step st' c continuation' n
                                        else Success (st, continuation)
           | <{ c1 !! c2 }> => ceval_step st c1 ((st,c2)::continuation) n
           | <{ b -> c1 }> => if beval st b
                              then ceval_step st c1 continuation n
                              else match continuation with
                                   | [] => Fail
                                   | (state', c2)::cont' => ceval_step state' <{ c2;c }> cont' n
                                   end
           end
  end.



(* Helper functions that help with running the interpreter *)
Inductive show_result : Type :=
  | OK (st: list (string*nat))
  | KO
  | OOG.

Open Scope string_scope.
Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step st c [] n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)]
  end.

(* Tests are provided to ensure that your interpreter is working for these examples *)
Example test_1: 
  run_interpreter (X !-> 5) <{skip}> 1 = OK [("X", 5); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_2: 
  run_interpreter (X !-> 5) <{ X:= X+1 }> 1 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_3: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 3 = OK [("X", 8); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_4: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 2 = OOG.
Proof. auto. Qed.

Example test_5:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 2 = KO.
Proof. auto. Qed.

Example test_6:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 1 = OOG.
Proof. auto. Qed.

Example test_7:
  run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_8:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 4 = OOG.
Proof. auto. Qed.

Example test_9:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 5 = OK [("X", 3); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_10:
  run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1)); X=2 -> skip }> 5 = OK [("X", 2); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_11:
  run_interpreter (X !-> 5) 
  <{  while ~(X = 0) do 
        X:=X-1; Y:=Y+1
      end;
      Y=5 -> skip
  }>
  8 
  = OK [("X", 0); ("Y", 5); ("Z", 0)].
Proof. auto. Qed.


(**
  2.2. DONE: Prove p1_equals_p2. Recall that p1 and p2 are defined in Imp.v

  Property Explanation:
  - There is an i0 (number of steps) such that for all i1 >= i0, the result of ceval_step
    for p1 and p2 is the same. Basically, the two programs are equivalent with a number of steps
    greater than or equal to i0.
*)

Theorem p1_equals_p2: forall st cont,
  (exists i0,
    (forall i1, i1 >= i0 -> ceval_step st p1 cont i1 =  ceval_step st p2 cont i1)).
Proof.
  intros st cont.
  exists 5.
  intros i1 H.
  destruct i1.
  - simpl. reflexivity.
  - destruct i1.
    --  lia.
    -- destruct i1.
       --- lia.
       --- destruct i1.
           ---- lia.
           ---- destruct i1.
               ----- lia.
               ----- simpl. reflexivity.
Qed.

(**
  2.3. DONE: Prove ceval_step_more.

  Property Explanation:
  - If the result of ceval_step for a program c with i1 steps is Success (st', cont'),
    then for all i2 >= i1, the result of ceval_step for the same program c with i2 steps
    is also Success (st', cont'). Basically, if the program terminates in i1 steps, it will
    also terminate in i2 steps, for all i2 >= i1.
*)

Theorem ceval_step_more: forall i1 i2 st st' c cont cont',
  i1 <= i2 ->
  ceval_step st c cont i1 = Success (st', cont') ->
  ceval_step st c cont i2 = Success (st', cont').
Proof.
  induction i1 as [| i1' ]; intros i2 st st' c cont cont' Hle Hceval.
  - (* i1 = 0 *)
    simpl in Hceval. discriminate Hceval.
  - (* i1 = S i1' *)
    destruct i2 as [| i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    -- (* skip *)
      simpl in Hceval. inversion Hceval. reflexivity.
    -- (* := *)
      simpl in Hceval. inversion Hceval. reflexivity.
    -- (* ; *)
      simpl in Hceval. simpl. destruct (ceval_step st c1 cont i1') eqn:Heq1.
      --- destruct s. apply (IHi1' i2') in Heq1; try assumption.
          rewrite Heq1. simpl. apply IHi1' with (i2:=i2') in Hceval; try assumption.
      --- discriminate Hceval.
      --- discriminate Hceval.
    -- (* if *)
      simpl in Hceval. simpl. destruct (beval st b); apply ( IHi1' i2') in Hceval; assumption.
    -- (* while *)
      simpl in Hceval. destruct (beval st b) eqn:Heq.
      --- simpl. rewrite Heq. destruct (ceval_step st c cont i1') eqn:Heq1.
          ---- destruct s. apply IHi1' with (i2:=i2') in Heq1; try assumption.
              rewrite Heq1. simpl. apply IHi1' with (i2:=i2') in Hceval; try assumption.
          ---- discriminate Hceval.
          ---- discriminate Hceval.
      --- simpl. rewrite Heq. try assumption.
    -- (* !! *)
      simpl in Hceval. destruct (ceval_step st <{ c1 !! c2 }> cont i1') eqn:Heq1.
      --- destruct i1'. discriminate Hceval. simpl. apply IHi1' with (i2:=i2') in Hceval; try assumption.
      --- destruct i1'. discriminate Hceval. simpl. apply IHi1' with (i2:=i2') in Hceval; try assumption.
      --- destruct i1'. discriminate Hceval. simpl. apply IHi1' with (i2:=i2') in Hceval; try assumption.
    -- (* -> *)
      simpl in Hceval. destruct (beval st b) eqn:Heq.
      --- simpl. rewrite Heq. apply IHi1' with (i2:=i2') in Hceval; try assumption.
      --- simpl. rewrite Heq. destruct cont.
          ---- discriminate Hceval.
          ---- destruct p. destruct i1'. discriminate Hceval.
              simpl. apply IHi1' with (i2:=i2') in Hceval; try assumption.
Qed.
