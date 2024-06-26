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
3. DONE: Define the relational semantics (ceval) to support the required constructs.
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
| E_GuardFalseFail : forall st b c,
    beval st b = false ->
    st / [] =[ b -> c ]=> empty_st / [] / Fail (* <--- empty_st because we assume that failure always yields it *)
| E_GuardTrue : forall st q st' q' b c r,
    beval st b = true ->
    st / q =[ c ]=> st' / q' / r ->
    st / q =[ b -> c ]=> st' / q' / r
| E_GuardFalseBacktrackTrue : forall st b c st_alt c_alt tq_alt st' q' r' st'' q'' r'',
    beval st b = false ->
    st_alt / tq_alt =[ c_alt ]=> st' / q' / r' ->
    beval st' b = true ->
    st' / q' =[ b -> c ]=> st'' / q'' / r'' ->
    st / ((st_alt,c_alt)::tq_alt) =[ b -> c ]=> st'' / q'' / r''
| E_Nondet1 : forall st q c1 c2 st' q' r,
    st / q =[ c1 ]=> st' / q' / r ->
    st / q =[ c1 !! c2 ]=> st' / ((st,c2)::q') / r
| E_Nondet2 : forall st q c1 c2 st' q' r,
    st / q =[ c2 ]=> st' / q' / r ->
    st / q =[ c1 !! c2 ]=> st' / ((st,c1)::q') / r


(* Hint: follow the same structure as shown in the chapter Imp *)
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).


(**
  3.1. DONE: Use the new relational semantics to prove the examples
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
  exists [].
  apply E_Seq with (X !-> 1) [(empty_st, <{X := 2}>)] Success.
  - apply E_Nondet1. apply E_Asgn. reflexivity.
  - apply E_GuardFalseBacktrackTrue with (X !-> 2) [] Success; try reflexivity.
    -- apply E_Asgn. reflexivity.
    -- apply E_GuardTrue.
      --- reflexivity.
      --- replace (X !-> 3) with (X !-> 3; X !-> 2).
        ---- apply E_Asgn. reflexivity.
        ---- apply t_update_shadow.
Qed.

Example ceval_example_guard4: exists q,
  empty_st / [] =[
    (X := 1 !! X := 2);
    (X = 2) -> X:=3
  ]=> (X !-> 3) / q / Success.
Proof.
  exists [(empty_st, <{X := 1}>)].
  apply E_Seq with (X !-> 2) [(empty_st, <{X := 1}>)] Success.
  - apply E_Nondet2. apply E_Asgn. reflexivity.
  - apply E_GuardTrue.
    -- reflexivity.
    -- replace (X !-> 3) with (X !-> 3; X !-> 2).
      --- apply E_Asgn. reflexivity.
      --- apply t_update_shadow. 
Qed.


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
  3.2. DONE: Prove the properties below.
*)

Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  split; unfold cequiv_imp; intros; exists q2; inversion H; subst; simpl in H.
  - inversion H2; subst.
    simpl in H2. simpl in H8.
    inversion H8; subst.
    simpl in H9; discriminate.
    inversion H10; subst.
    -- apply E_Asgn. reflexivity.
    -- simpl in H3. discriminate.
  - apply E_Seq with (X !-> 2;st1) q2 Success.
    -- apply E_Asgn. reflexivity.
    -- apply E_GuardTrue.
       --- simpl. reflexivity.
       --- apply E_Skip.
Qed.

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  split; unfold cequiv_imp; intros; inversion H; subst.
  - inversion H2; subst.
    inversion H8; subst.
    inversion H9; subst.
    simpl in H3.
    -- discriminate.
    -- inversion H13; subst.
       inversion H15; subst; try discriminate.
       --- inversion H12; subst.
           exists q1. apply E_Asgn. reflexivity.
    -- inversion H8; subst.
       inversion H11; subst.
       --- inversion H9; subst.
           exists q'. apply E_Asgn. reflexivity.
       --- inversion H9; subst.
           inversion H8; subst; discriminate.
  - exists ((st1, <{ X := 1 }>) :: q2). 
    apply E_Seq with (X !-> 2; st1) ((st1, <{ X := 1 }>) :: q2) Success.
    -- apply E_Nondet2. apply E_Asgn. reflexivity.
    -- apply E_GuardTrue.
       --- simpl. reflexivity.
       --- apply E_Skip.
Qed.


Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  intros c; split; unfold cequiv_imp; intros.
  - inversion H; subst; exists q'; apply H7.
  - exists ((st1,c)::q2). apply E_Nondet1. apply H.
Qed.

Lemma choice_comm: forall c1 c2,
  <{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  intros c1 c2; split; unfold cequiv_imp; intros; inversion H; subst.
  - exists ((st1,c2)::q'). apply E_Nondet2. apply H7.
  - exists ((st1,c1)::q'). apply E_Nondet1. apply H7.
  - exists ((st1,c1)::q'). apply E_Nondet2. apply H7.
  - exists ((st1,c2)::q'). apply E_Nondet1. apply H7.
Qed.

Lemma choice_assoc: forall c1 c2 c3,
  <{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  split; unfold cequiv_imp; intros; inversion H; subst.
  - inversion H7; subst.
    -- exists ((st1,<{ c2 !! c3 }>)::q'0). apply E_Nondet1. apply H8.
    -- exists ((st1,c1)::(st1,c3)::q'0). apply E_Nondet2. apply E_Nondet1. apply H8.
  - exists ((st1,c1)::(st1,c2)::q'). apply E_Nondet2. apply E_Nondet2. apply H7.
  - exists ((st1,c3)::(st1,c2)::q'). apply E_Nondet1. apply E_Nondet1. apply H7.
  - inversion H7; subst.
    -- exists ((st1,c3)::(st1,c1)::q'0). apply E_Nondet1. apply E_Nondet2. apply H8.
    -- exists ((st1,<{ c1 !! c2 }>)::q'0). apply E_Nondet2. apply H8.
Qed.

Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  intros c1 c2 c3; split; unfold cequiv_imp; intros st1 st2 q1 q2 r.
  - intros H. inversion H; subst; inversion H8; subst.
    exists ((st1,<{c1;c3}>)::q'). eapply E_Nondet1.
    -- eapply E_Seq.
       --- apply H2.
       --- apply H9.
    -- exists ((st1,<{c1;c2}>)::q'). eapply E_Nondet2.
       --- eapply E_Seq.
           ---- apply H2.
           ---- apply H9.
  - intros H. inversion H; subst; inversion H7; subst.
    -- exists ((st3,c3)::q'). apply E_Seq with st3 q2 r1.
       --- apply H2.
       --- apply E_Nondet1. apply H9.
    -- exists ((st3,c2)::q'). apply E_Seq with st3 q2 r1.
       --- apply H2.
       --- apply E_Nondet2. apply H9.
Qed.

Lemma choice_congruence: forall c1 c1' c2 c2',
  c1 == c1' -> c2 == c2' ->
  <{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  intros c1 c1' c2 c2' H1 H2.
  split; unfold cequiv_imp; intros; inversion H; subst.
  - apply H1 in H9. 
    inversion H9.
    exists ((st1,c2')::x).
    apply E_Nondet1.
    apply H0.
  - apply H2 in H9. 
    inversion H9.
    exists ((st1,c1')::x).
    apply E_Nondet2.
    apply H0.
  - apply H1 in H9. 
    inversion H9.
    exists ((st1,c2)::x).
    apply E_Nondet1.
    apply H0.
  - apply H2 in H9. 
    inversion H9.
    exists ((st1,c1)::x).
    apply E_Nondet2.
    apply H0.
Qed.
