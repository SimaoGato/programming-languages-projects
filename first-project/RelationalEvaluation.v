From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).

(* 
3. TODO: Define the relational semantics (ceval) to support the required constructs.
*)

Inductive ceval : com -> state -> list (state * com) -> 
                  result -> state -> list (state * com) -> Prop :=
| E_Skip : forall st q,
    st / q =[ skip ]=> st / q / Success
| E_Asgn : forall st q X a n,
    aeval st a = n ->
    st / q =[ X := a ]=> (X !-> n ; st) / q / Success 
| E_Seq : forall c1 c2 st1 q1 st2 q2 st3 q3 r1 r2,
    st1 / q1 =[ c1 ]=> st2 / q2 / r1 ->
    st2 / q2 =[ c2 ]=> st3 / q3 / r2 ->
    st1 / q1 =[ c1 ; c2 ]=> st3 / q3 / r2
| E_IfTrue : forall st q st' q' b c1 c2 r,
    beval st b = true ->
    st / q =[ c1 ]=> st' / q' / r ->
    st / q =[ if b then c1 else c2 end ]=> st' / q' / r
| E_IfFalse : forall st q st' q' b c1 c2 r,
    beval st b = false ->
    st / q =[ c2 ]=> st' / q' / r ->
    st / q =[ if b then c1 else c2 end ]=> st' / q' / r
| E_WhileFalse : forall b st q c,
    beval st b = false ->
    st / q =[ while b do c end ]=> st / q / Success
| E_WhileTrue : forall c st1 q1 st2 q2 st3 q3 r1 r2 b,
    beval st1 b = true ->
    st1 / q1 =[ c ]=> st2 / q2 / r1 ->
    st2 / q2 =[ while b do c end ]=> st3 / q3 / r2 ->
    st1 / q1 =[ while b do c end ]=> st3 / q3 / r2

(* TODO: Thins are probably wrong/inc *)
| E_Nondet1 : forall st q c1 c2 st' q' r,
    st / q =[ c1 ]=> st' / q' / r ->
    st / q =[ c1 !! c2 ]=> st' / ((st',c2)::q') / r
| E_Nondet2 : forall st q c1 c2 st' q' r,
    st / q =[ c2 ]=> st' / q' / r ->
    st / q =[ c1 !! c2 ]=> st' / ((st',c1)::q') / r
| E_GuardTrue : forall st q st' q' b c r,
    beval st b = true ->
    st / q =[ c ]=> st' / q' / r ->
    st / q =[ (b -> c) ]=> st' / q' / r
| E_GuardFalse : forall st1 q c c' st0 q0 st2 q' r b,
    beval st1 b = false ->
    st0 / ((st0,c')::q0) =[ c' ]=> st2 / q' / r ->
    st1 / q =[ (b -> c) ]=> st2 / q' / Fail
| E_GuardFalseFail : forall st1 c st0 b,
    beval st1 b = false ->
    st1 / [] =[ (b -> c) ]=> st0 / [] / Fail

(* TODO. Hint: follow the same structure as shown in the chapter Imp *)
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).


(**
  3.1. TODO: Use the new relational semantics to prove the examples
             ceval_example_if, ceval_example_guard1, ceval_example_guard2,
             ceval_example_guard3 and ceval_example_guard4.
*)

Example ceval_example_if:
  empty_st / [] =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2) [] Success.
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse.
    -- reflexivity. 
    -- apply E_Asgn. reflexivity.
Qed.


Example ceval_example_guard1:
  empty_st / [] =[
    X := 2;
    (X = 1) -> X:=3
  ]=> (empty_st) / [] / Fail.
Proof.
  apply E_Seq with (X !-> 2) [] Success.
  - apply E_Asgn. reflexivity.
  - apply E_GuardFalseFail. reflexivity.
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2) [] Success.
  - apply E_Asgn. reflexivity.
  - apply E_GuardTrue.
    -- reflexivity.
    -- apply E_Asgn. reflexivity.
Qed. 

Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  (* TODO *)
Admitted.


Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  (* TODO *)
Admitted.



(* 3.2. Behavioral equivalence *)

Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st1 st2 : state) q1 q2 result,
(st1 / q1 =[ c1 ]=> st2 / q2 / result) ->
exists q3, 
(st1 / q1 =[ c2 ]=> st2 / q3 / result).

Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


(**
  3.2. TODO: Prove the properties below.
*)

Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  (* TODO *)
Admitted.

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  (* TODO *)
Admitted.


Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  intros c; split; unfold cequiv_imp; intros.
  - inversion H; subst.
    -- exists q'. apply H7.
    -- exists q'. apply H7.
  - exists ((st2,c)::q2). apply E_Nondet1. apply H.
Qed.

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  intros c1 c2; split; unfold cequiv_imp; intros.
  - inversion H; subst.
    -- exists ((st2,c2)::q'). apply E_Nondet2. apply H7.
    -- exists ((st2,c1)::q'). apply E_Nondet1. apply H7.
  - inversion H; subst.
    -- exists ((st2,c1)::q'). apply E_Nondet2. apply H7.
    -- exists ((st2,c2)::q'). apply E_Nondet1. apply H7.
Qed.

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
(* TODO *)
Qed.


Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  (* TODO *)
Qed.

Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  (* TODO *)
Qed.
