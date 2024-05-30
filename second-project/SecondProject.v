(* Programming Languages: Project 2
 * 
 * You are required to complete the 12 exercises below. 
 *
 * Important:
 *  - Do not change any existing code nor the type of any function 
 *    or theorem, otherwise you might not get any points. If in doubt, ask
 *    a member of the teaching team.
 *  - Do not delete any comments, except those marked as (*TODO*)
 *  - You can add new code or new lemmas (but make sure there's a good 
 *    reason for doing so)
 *  - Your proofs should be as simple and short as possible. After finishing
 *    all the required proofs, consider whether you can make them shorter and
 *    more automated.
 *
 * All you have to do is to solve the exercises that are clearly
 * marked as so (search for the string EXERCISE). 
 * You have to replace the comments (*TODO*) by your own solution.
 *
 * We assume that you will follow the established code of ethics and 
 * submit your own work. Any student might be asked to present and 
 * explain their submission.
 *
 * This component is worth 20 points. Each question
 * shows how many points it is worth.
 *
 * Deadline: 31st May 2024, 23:59
 *)


(* We import the files from the book Software Foundations (vol. 2). 
   To make it easier, you might want to copy this file to the same 
   directory as the book. If you have problems importing the files
   below, get in touch with the teaching team. *)

Set Warnings "-notation-overridden,-parsing,-require-in-module,-fragile".

From SecondProject Require Import Maps.
From Coq Require Import Arith.PeanoNat. Import Nat.
From SecondProject Require Import Imp.
From SecondProject Require Import Hoare.
From SecondProject Require Import Smallstep.

Module SecondProject.

(* In this Coq Assessment, we will extend IMP with three new commands:

  - The first two are [assert] and [assume]. Both commands are ways
    to indicate that a certain statement should hold any time this part
    of the program is reached. However they differ as follows:

     - If an [assert] statement fails, it causes the program to go into
       an error state and exit.

     - If an [assume] statement fails, the program fails to evaluate
       at all. In other words, the program gets stuck and has no
       final state.

  - Non-deterministic choice [c1 !! c2]. This chooses non-deterministically
    between [c1] and [c2]. For example, if we have [(X := 1) !! (X := 2)],
    only one of the assignments will be executed: on termination, [X] will
    either have value 1 or value 2 (only one of the assignments execute!)
*)



(* ################################################################# *)
(* IMP is extended with three new commands, as shown below           *)
(* ################################################################# *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CAssert (b : bexp)  (* <- new *)
  | CAssume (b : bexp)  (* <- new *)
  | CNonDetChoice (c1 c2: com).  (* <- new *)

(* We now define notations. *)  
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** We can use the new notation defined here: *)
Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
Notation "c1 !! c2" :=
  (CNonDetChoice c1 c2)
    (in custom com at level 90, right associativity) : com_scope.

(** To define the behavior of [assert] and [assume], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.


(* ################################################################# *)
(* EXERCISE 1 (1 point): Define a relational evaluation (big-step    *)
(*                       semantics). Most rules are given. Note the  *)
(*                       use of RNormal / RError.                    *)
(* ################################################################# *)


Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* DONE: *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_AssumeTrue : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st
      (*| E_AssumeFalse : forall st b,
      beval st b = false ->
         st =[ assume b ]=> RError*) (* This rule is not needed because the program gets stuck? *)
  | E_NonDetChoice1 : forall st c1 c2 r,
      st =[ c1 ]=> r ->
      st =[ c1 !! c2 ]=> r
  | E_NonDetChoice2 : forall st c1 c2 r,
      st =[ c2 ]=> r ->
      st =[ c1 !! c2 ]=> r

where "st '=[' c ']=>' r" := (ceval c st r).


(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').


Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(* ################################################################## *)
(* EXERCISE 2 (2 points): Prove properties involving [assert] and     *)
(*            [assume]. To test your understanding of the new         *)
(*            operators, prove [assume_false] and                     *)
(*            [assert_implies_assume].                                *)
(*            For the first, show that any triple where we assume     *)
(*            a false condition is always valid.                      *)
(*            For the second, prove that any triple for [assert]      *)
(*            also works for [assume].                                *)
(* ################################################################## *)

Theorem assume_false: forall P Q b,
       (forall st, beval st b = false) ->
       ({{P}} assume b {{Q}}).
Proof.
  (* DONE: *)
  unfold hoare_triple. intros. 
  inversion H0. subst. rewrite H in H3.
  discriminate H3.
Qed.

Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
  (* DONE: *)
  unfold hoare_triple. intros.
  inversion H0; subst.
  apply H with (st := st) (r := RNormal st); try assumption.
  apply E_AssertTrue. apply H3.
Qed.


(* ################################################################# *)
(* EXERCISE 3 (4 points): Define Hoare rules for the new operators   *)
(*                        in IMP. See sub-exercises below.           *)
(* ################################################################# *)

(** For your benefit, we provide proofs for the old hoare rules
    adapted to the new semantics. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  eexists. split; try reflexivity. assumption.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  (*- apply (Himp st Hpre).*)
  - apply Himp in Hpre. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ']].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ]].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _]].
     inversion C.
Qed.

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split. reflexivity. assumption.
Qed.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(** That is (unwrapping the notations):

      Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
*)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.


Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (<{while b do c end}>) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split. reflexivity. split.
    assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2. reflexivity.
    clear IHHe2 He2 r.
    unfold hoare_triple in Hhoare.
    apply Hhoare in He1.
    + destruct He1 as [st1 [Heq Hst1]].
        inversion Heq; subst.
        assumption.
    + split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _]]. inversion C.
     + split; assumption.
Qed.

(** (End of proofs given.) *)

(* ================================================================= *)
(* EXERCISE 3.1: State and prove [hoare_assert]                      *)
(* ================================================================= *)

(* DONE: Hoare proof rule for [assert] *)
Theorem hoare_assert: forall P (b: bexp),
  {{P /\ b}} assert b {{P}}.
Proof.
  (* DONE: *)
  unfold hoare_triple.
  intros.
  inversion H ; subst.
  - exists st. split; try reflexivity.
    destruct H0.
    apply H0.
  - destruct H0. rewrite H1 in H2. discriminate H2.
Qed.

(* ================================================================= *)
(* EXERCISE 3.2: State and prove [hoare_assume]                      *)
(* ================================================================= *)

(* DONE: Hoare proof rule for [assume] *)
Theorem hoare_assume: forall (P:Assertion) (b:bexp),
  {{b -> P}} assume b {{P}}.
Proof.
  (* DONE: *)
  unfold hoare_triple.
  intros.
  inversion H; subst.
  exists st. split; try reflexivity.
  simpl in H0. apply H0 in H2. apply H2.
Qed.

(* ================================================================= *)
(* EXERCISE 3.3: State and prove [hoare_choice]                      *)
(* ================================================================= *)

(* DONE: Hoare proof rule for [c1 !! c2] *)
Theorem hoare_choice' : forall P c1 c2 Q,
  {{P}} c1 {{Q}} ->
  {{P}} c2 {{Q}} ->
  {{P}} c1 !! c2 {{Q}}.
Proof.
  (* DONE: *)
  unfold hoare_triple.
  intros.
  inversion H1; subst.
  - apply H with (st := st).
    -- apply H7.
    -- apply H2.
  - apply H0 with (st := st).
    -- apply H7.
    -- apply H2.
Qed.

(* ================================================================= *)
(* EXERCISE 3.4: Use the proof rules defined to prove the following  *)
(*               example. Also, add a comment explaining in your own *)
(*               words what this example is demonstrating.           *)                                            
(* ================================================================= *)

(*
  DONE: Here we're demonstrating that when X = 1 and after non-deterministically
  choosing to increment it by one or two, the value of X will either be 2 or 3.
*)
Example hoare_choice_example:
  {{ X = 1 }}
  X := X + 1 !! X := X + 2
  {{ X = 2 \/ X = 3 }}.
Proof.
  (* DONE: *)
  apply hoare_choice'; simpl; eapply hoare_consequence_pre.
    -- apply hoare_asgn.
    -- unfold "->>". intros st H. simpl. left.
      rewrite t_update_eq. simpl. rewrite H. reflexivity.
    -- apply hoare_asgn.
    -- unfold "->>". intros st H. simpl. right.
      rewrite t_update_eq. simpl. rewrite H. reflexivity.
Qed.


(* ################################################################# *)
(* EXERCISE 4 (1.5 points): Define a relational evaluation (small-step *)
(*                        semantics). Some rules are given.          *)
(* ################################################################# *)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).



Inductive cstep : (com * result)  -> (com * result) -> Prop :=
  (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st -->a a' ->
      <{ i := a }> / RNormal st --> <{ i := a' }> / RNormal st
  | CS_Asgn : forall st i n,
      <{ i := (ANum n) }> / RNormal st --> <{ skip }> / RNormal (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st -->b b' ->
      <{if b then c1 else c2 end }> / RNormal st 
      --> <{ if b' then c1 else c2 end }> / RNormal st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b c1,
          <{while b do c1 end}> / st 
      --> <{ if b then (c1; while b do c1 end) else skip end }> / st

  (* DONE: *)
  | CS_AssertStep : forall st b b',
      b / st -->b b' ->
      <{ assert b }> / RNormal st --> <{ assert b' }> / RNormal st 
  | CS_AssertTrue : forall st,
      <{ assert true }> / RNormal st --> <{ skip }> / RNormal st
  | CS_AssertFalse : forall st,
      <{ assert false }> / RNormal st --> <{ skip }> / RError
  | CS_AssumeStep : forall st b b',
      b / st -->b b' ->
      <{ assume b }> / RNormal st --> <{ assume b' }> / RNormal st
  | CS_AssumeTrue : forall st,
      <{ assume true }> / RNormal st --> <{ skip }> / RNormal st
  | CS_NonDetChoice1 : forall st c1 c2,
      <{ c1 !! c2 }> / st --> c1 / st
  | CS_NonDetChoice2 : forall st c1 c2,
      <{ c1 !! c2 }> / st --> c2 / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).


(* ################################################################# *)
(* EXERCISE 5 (1 point): Show that the program [prog1] can           *)
(*            successfully terminate in a state where [X=2].         *)
(*            Use the rules defined in [cstep].                      *)
(*            You can use [multi_step] and [multi_refl].             *) 
(* ################################################################# *)


(* We start with an example of a proof about a simple program that uses
the rules already provided. *)

Definition prog0 : com :=
  <{ X := X + 1 ; X := X + 2 }>.

Example prog0_example:
  exists st',
       prog0 / RNormal (X !-> 1) -->* <{ skip }> / RNormal st'
    /\ st' X = 4.
Proof.
  eexists. split.
  unfold prog0.

  (* Sequence and X := X+1*)
  eapply multi_step. apply CS_SeqStep. 
  apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_SeqStep. apply CS_AssStep. apply AS_Plus.
  simpl. eapply multi_step. apply CS_SeqStep. apply CS_Asgn. eapply multi_step. 
  apply CS_SeqFinish.

  (* X := X + 2 *)
  eapply multi_step. apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_AssStep. apply AS_Plus.
  simpl. eapply multi_step. apply CS_Asgn. eapply multi_refl.

  reflexivity.
Qed. 

  
Definition prog1 : com :=
  <{ 
  assume (X = 1);
  ((X := X + 1) !! (X := 3));
  assert (X = 2)
  }>.

Example prog1_example1:
  exists st',
       prog1 / RNormal (X !-> 1) -->* <{ skip }> / RNormal st'
    /\ st' X = 2.
Proof.
  (* DONE: *)
  eexists. split.
  unfold prog1.

  (* Assume *)
  eapply multi_step. apply CS_SeqStep. apply CS_AssumeStep. apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_SeqStep. apply CS_AssumeStep. apply BS_Eq.
  eapply multi_step. apply CS_SeqStep. apply CS_AssumeTrue.
  eapply multi_step. apply CS_SeqFinish.

  (* Non-deterministic choice *)
  eapply multi_step. apply CS_SeqStep. apply CS_NonDetChoice1.
  eapply multi_step. apply CS_SeqStep. apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_SeqStep. apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_SeqStep. apply CS_Asgn.
  eapply multi_step. apply CS_SeqFinish.

  (* Assert *)
  eapply multi_step. apply CS_AssertStep. apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_AssertStep. apply BS_Eq.
  eapply multi_step. apply CS_AssertTrue. apply multi_refl.
  reflexivity.
Qed.

(* ################################################################# *)
(* EXERCISE 6 (1 point): Prove the following property.            *)
(* ################################################################# *)

Lemma one_step_aeval_a: forall st a a',
  a / st -->a a' ->
  aeval st a = aeval st a'.
Proof.
  (* DONE:(Hint: you can prove this by induction on a) *)
  intros.
  induction H; simpl; try reflexivity; try rewrite IHastep; try reflexivity.
Qed.


(* ================================================================= *)
(* Decorated Programs                                                *)
(* ================================================================= *)

(* We now go back to Hoare Logic and Decorated Programs. The goal is
   see how one can formalize decorated programs and mostly automate
   the verification process. 

   This part is taken from the chapter "Hoare Logic, Part II":
   https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html

   We work on a separate module called DCom. Most of the comments below
   are text from the book.
*)

Module DCom.

(* ================================================================= *)
(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of
    the syntax of commands that includes embedded assertions --
    decorations.  We call the new commands _decorated commands_, or
    [dcom]s.

 Concretely, we decorate programs as follows... *)

(** - The [skip] command is decorated only with its postcondition

      skip {{ Q }}

      on the assumption that the precondition will be provided by the
      context.

      We carry the same assumption through the other syntactic forms:
      each decorated command is assumed to carry its own postcondition
      within itself but take its precondition from its context in
      which it is used.
*)

(** - Sequences [d1 ; d2] need no additional decorations.

      Why?  Inside [d2] there will be a postcondition; this serves as
      the postcondition of [d1;d2].  Inside [d1] there will also be
      a postcondition, which additionally serves as the precondition
      for [d2]. *)

(** - An assignment [X := a] is decorated only with its postcondition:

      X := a {{ Q }}
*)

(** - A conditional [if b then d1 else d2] is decorated with a
      postcondition for the entire statement, as well as preconditions
      for each branch:

      if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }}
*)

(** - A loop [while b do d end] is decorated with its postcondition
      and a precondition for the body:

      while b do {{ P }} d end {{ Q }}

      The postcondition embedded in [d] serves as the loop invariant. *)

(** - Implications [->>] can be added as decorations either for a
      precondition

      ->> {{ P }} d

      or for a postcondition

      d ->> {{ Q }}

      The former is waiting for another precondition to eventually be
      supplied (e.g., [{{ P'}} ->> {{ P }} d]); the latter relies on
      the postcondition already embedded in [d]. *)



(* ################################################################# *)
(* EXERCISE 7 (1 point): Extend [dcom] with the decorated            *)
(*                       versions of the three new commands and      *)
(*                       define new notation for the new commands.   *)
(* ################################################################# *)

(** Here's the formal syntax of decorated commands: *)

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *)
| DCAssert (b : bexp) (Q : Assertion)
| DCAssume (b : bexp) (Q : Assertion)
| DCNonDetChoice (d1 d2 : dcom).

(** To provide the initial precondition that goes at the very top of a
    decorated program, we introduce a new type [decorated]: *)

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

(** To avoid clashing with the existing [Notation]s for ordinary
    [com]mands, we introduce these notations in a new grammar scope
    called [dcom]. *)


Declare Scope dcom_scope.
Notation "'skip' {{ P }}"
      := (DCSkip P)
      (in custom com at level 0, P constr) : dcom_scope.
Notation "l ':=' a {{ P }}"
      := (DCAsgn l a P)
      (in custom com at level 0, l constr at level 0,
          a custom com at level 85, P constr, no associativity) : dcom_scope.
Notation "'while' b 'do' {{ Pbody }} d 'end' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
            (in custom com at level 89, b custom com at level 99,
            Pbody constr, Ppost constr) : dcom_scope.
Notation "'if' b 'then' {{ P }} d 'else' {{ P' }} d' 'end' {{ Q }}"
      := (DCIf b P d P' d' Q)
            (in custom com at level 89, b custom com at level 99,
                P constr, P' constr, Q constr) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (in custom com at level 12, right associativity, P constr) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (in custom com at level 10, right associativity, P constr) : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
      (in custom com at level 90, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (in custom com at level 91, P constr) : dcom_scope.


(* DONE: notation for the three new constructs *)
(* TODO: NOT SURE ABOUT THE LEVELS AND STUFF!!!!! *)
Notation "'assert' l {{ P }}"
      := (DCAssert l P)
      (in custom com at level 90, l constr, P constr) : dcom_scope.
Notation "'assume' l {{ P }}"
      := (DCAssume l P)
      (in custom com at level 90, l constr, P constr) : dcom_scope.
Notation "d1 '!!' d2"
      := (DCNonDetChoice d1 d2)
      (in custom com at level 90, right associativity) : dcom_scope.

Local Open Scope dcom_scope.

(** An example [decorated] program that decrements [X] to [0]: *)

Example dec_while : decorated :=
  <{
  {{ True }}
    while X <> 0
    do
                 {{ True /\ (X <> 0) }}
      X := X - 1
                 {{ True }}
    end
  {{ True /\  X = 0}} ->>
  {{ X = 0 }} }>.



(* ################################################################# *)
(* EXERCISE 8 (1 point): Extend the functions [extract] and          *)
(*                           [post] considering the new constructs.  *)
(* ################################################################# *)

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _           => CSkip
  | DCSeq d1 d2        => CSeq (extract d1) (extract d2)
  | DCAsgn X a _       => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (extract d1) (extract d2)
  | DCWhile b _ d _    => CWhile b (extract d)
  | DCPre _ d          => extract d
  | DCPost d _         => extract d
  (* DONE: *)
  | DCAssert b _      => CAssert b
  | DCAssume b _      => CAssume b
  | DCNonDetChoice d1 d2 => CNonDetChoice (extract d1) (extract d2)
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated p d => extract d
  end.

Example extract_while_ex :
    extract_dec dec_while
  = <{while X <> 0 do X := X - 1 end}>.
Proof.
  unfold dec_while.
  reflexivity.
Qed.

(** It is also straightforward to extract the precondition and
    postcondition from a decorated program. *)

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated p d => p
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip p                => p
  | DCSeq _ d2              => post d2
  | DCAsgn _ _ Q            => Q
  | DCIf  _ _ _ _ _ Q       => Q
  | DCWhile _ _ _ Q         => Q
  | DCPre _ d               => post d
  | DCPost _ Q              => Q
  (* DONE: *)
  | DCAssert _ Q           => Q
  | DCAssume _ Q           => Q
  | DCNonDetChoice d1 d2   => post d1 \/ post d2
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated p d => post d
  end.

Example pre_dec_while : pre_dec dec_while = True.
Proof. reflexivity. Qed.

Example post_dec_while : post_dec dec_while = (X = 0)%assertion.
Proof. reflexivity. Qed.

(** We can then express what it means for a decorated program to
    be correct as follows: *)

Definition outer_triple_valid (dec : decorated) :=
  {{pre_dec dec}} extract_dec dec {{post_dec dec}}.

Example dec_while_triple_correct :
     outer_triple_valid dec_while
   =
     {{ True }}
       while X <> 0 do X := X - 1 end
     {{ X = 0 }}.
Proof. reflexivity. Qed.

(** Remember that the outer Hoare triple of a decorated program is
    just a [Prop]; thus, to show that it is _valid_, we need to
    produce a proof of this proposition.

    We will do this by extracting "proof obligations" from the
    decorations sprinkled through the program.

    These obligations are often called _verification conditions_,
    because they are the facts that must be verified to see that the
    decorations are locally consistent and thus constitute a proof of
    correctness. *)

(* ================================================================= *)
(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a decorated command
    [d] together with a precondition [P] and returns a _proposition_
    that, if it can be proved, implies that the triple

     {{P}} (extract d) {{post d}}

    is valid.

    It does this by walking over [d] and generating a big conjunction
    that includes

    - local consistency checks for each form of command, plus

    - uses of [->>] to bridge the gap between the assertions found
      inside a decorated command and the assertions imposed by its
      context; these uses correspond to applications of the
      consequence rule. *)

(** - The decorated command

        skip {{Q}}

      is locally consistent with respect to a precondition [P] if
      [P ->> Q].
*)

(** - The sequential composition of [d1] and [d2] is locally
      consistent with respect [P] if [d1] is locally consistent with
      respect to [P] and [d2] is locally consistent with respect to
      the postcondition of [d1]. *)

(** - An assignment

        X := a {{Q}}

      is locally consistent with respect to a precondition [P] if:

        P ->> Q [X |-> a]
*)

(** - A conditional

      if b then {{P1}} d1 else {{P2}} d2 end

      is locally consistent with respect to precondition [P] if

         (1) [P /\ b ->> P1]

         (2) [P /\ ~b ->> P2]

         (3) [d1] is locally consistent with respect to [P1]

         (4) [d2] is locally consistent with respect to [P2]
*)
(** - A loop

      while b do {{Q}} d end {{R}}

      is locally consistent with respect to precondition [P] if:

         (1) [P ->> post d]

         (2) [post d /\ b ->> Q]

         (3) [post d /\ ~b ->> R]

         (4) [d] is locally consistent with respect to [Q]
*)

(** - A command with an extra assertion at the beginning

       --> {{Q}} d

      is locally consistent with respect to a precondition [P] if:

        (1) [P ->> Q]

        (1) [d] is locally consistent with respect to [Q]
*)

(** - A command with an extra assertion at the end

         d ->> {{Q}}

      is locally consistent with respect to a precondition [P] if:

        (1) [d] is locally consistent with respect to [P]

        (2) [post d ->> Q]
*)

(* ################################################################# *)
(* EXERCISE 9 (2 points): Extend [verification_conditions],          *)
(*                           considering the three new constructs.   *)
(* ################################################################# *)


Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
      (P ->> Q)
  | DCSeq d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
      (P ->> Q [X |-> a])
  | DCIf b P1 d1 P2 d2 Q =>
      ((P /\ b) ->> P1)%assertion
      /\ ((P /\ ~ b) ->> P2)%assertion
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Pbody d Ppost =>
      (* post d is the loop invariant and the initial
         precondition *)
      (P ->> post d)
      /\ ((post d  /\ b) ->> Pbody)%assertion
      /\ ((post d  /\ ~ b) ->> Ppost)%assertion
      /\ verification_conditions Pbody d
  | DCPre P' d =>
      (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
      verification_conditions P d
      /\ (post d ->> Q)
  (* DONE: *)
  | DCAssert b Q =>
      (P ->> (Q /\ b))%assertion
  | DCAssume b Q =>
      (P ->> (Q /\ b))%assertion
  | DCNonDetChoice d1 d2 =>
      verification_conditions P d1
      /\ verification_conditions P d2
  end.

(** The key theorem states that [verification_conditions] does its job
    correctly.  Not surprisingly, we need to use each of the Hoare
    Logic rules at some point in the proof. *)

(* ################################################################# *)
(* EXERCISE 10 (2 points): Prove the [verification_correct] for      *)
(*                            the new cases.                         *)
(* ################################################################# *)

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} extract d {{post d}}.
Proof.
  induction d; intros; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      + apply hoare_skip.
      + assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      + apply IHd2. apply H2.
      + apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse] ] ] ] ].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence; eauto.
      + eapply hoare_consequence; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1  Hd] ] ].
    eapply hoare_consequence; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre; eauto.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post; eauto.
  (* DONE: *)
  - (* Assert *)
    eapply hoare_consequence_pre.
      + apply hoare_assert.
      + assumption. 
  - (* Assume *)
    eapply hoare_consequence_pre.
      + apply hoare_assume.
      + unfold "->>". intros. apply H. apply H0.
  - (* NonDetChoice *)
    destruct H as [H1 H2].
    apply hoare_choice'; eapply hoare_consequence_post; eauto.
Qed.


(** Now that all the pieces are in place, we can define what it means
    to verify an entire program. *)

Definition verification_conditions_dec
              (dec : decorated) : Prop :=
  match dec with
  | Decorated p d => verification_conditions p d
  end.

Corollary verification_correct_dec : forall dec,
  verification_conditions_dec dec ->
  outer_triple_valid dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

(* ================================================================= *)
(** ** Automation *)
(** In [Hoare] we introduced a series of tactics named
    [assn_auto] to automate proofs involving assertions.

    The following declaration introduces a more sophisticated tactic
    that will help with proving assertions throughout the rest of this
    chapter.  You don't need to understand the details, but briefly:
    it uses [split] repeatedly to turn all the conjunctions into
    separate subgoals, tries to use several theorems about booleans
    and (in)equalities, then uses [eauto] and [lia] to finish off as
    many subgoals as possible. What's left after [verify_assn] does
    its thing should be just the "interesting parts" of the proof --
    which, if we're lucky, might be nothing at all! *)

From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
Set Default Goal Selector "!".
Ltac verify_assn :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                          destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.
    

(** Fortunately, our [verify_assn] tactic can generally take care of
    most or all of them. *)
Example vc_dec_while : verification_conditions_dec dec_while.
Proof. verify_assn. Qed.

(** To automate the overall process of verification, we can use
    [verification_correct] to extract the verification conditions, use
    [verify_assn] to verify them as much as it can, and finally tidy
    up any remaining bits by hand.  *)
Ltac verify :=
  intros;
  apply verification_correct;
  verify_assn.

(** Here's the final, formal proof that dec_while is correct. *)

Theorem dec_while_correct :
  outer_triple_valid dec_while.
Proof. verify. Qed.

(** Similarly, here is the formal decorated program for the "swapping
    by adding and subtracting" example that we saw earlier. *)

Definition swap_dec (m n:nat) : decorated :=
  <{
    {{ X = m /\ Y = n}} ->>
         {{ (X + Y) - ((X + Y) - Y) = n /\ (X + Y) - Y = m }}
    X := X + Y
         {{ X - (X - Y) = n /\ X - Y = m }};
    Y := X - Y
         {{ X - Y = n /\ Y = m }};
    X := X - Y
    {{ X = n /\ Y = m}}
  }>.

Theorem swap_correct : forall m n,
  outer_triple_valid (swap_dec m n).
Proof. verify. Qed.

(* For more examples, see chapter Hoare Logic, Part II. The next
   exercise is taken directly from there. *)


(* ################################################################# *)
(* EXERCISE 11 (0.5 points): Read the following example and:         *)
(*                            1) fill in the assertions in [sqrt_dec]*)
(*                            2) prove [sqrt_correct]                *)
(* ################################################################# *)

(* ================================================================= *)
(** ** Example: Finding Square Roots *)

(** The following program computes the integer square root of [X]
    by naive iteration:

    {{ X=m }}
      Z := 0;
      while (Z+1)*(Z+1) <= X do
        Z := Z+1
      end
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
*)

(** As we did before, we can try to use the postcondition as a
    candidate invariant, obtaining the following decorated program:

    (1)  {{ X=m }} ->>                   (a - second conjunct of (2) WRONG!)
    (2)  {{ 0*0 <= m /\ m<(0+1)*(0+1) }}
            Z := 0
    (3)            {{ Z*Z <= m /\ m<(Z+1)*(Z+1) }};
            while (Z+1)*(Z+1) <= X do
    (4)            {{ Z*Z<=m /\ (Z+1)*(Z+1)<=X }} ->>            (c - WRONG!)
    (5)            {{ (Z+1)*(Z+1)<=m /\ m<((Z+1)+1)*((Z+1)+1) }}
              Z := Z+1
    (6)            {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
            end
    (7)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) /\ ~((Z+1)*(Z+1)<=X) }} ->>  (b - OK)
    (8)  {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}

    This didn't work very well: conditions (a) and (c) both failed.
    Looking at condition (c), we see that the second conjunct of (4)
    is almost the same as the first conjunct of (5), except that (4)
    mentions [X] while (5) mentions [m]. But note that [X] is never
    assigned in this program, so we should always have [X=m]. We
    didn't propagate this information from (1) into the loop
    invariant, but we could!

    Also, we don't need the second conjunct of (8), since we can
    obtain it from the negation of the guard -- the third conjunct
    in (7) -- again under the assumption that [X=m].  This allows
    us to simplify a bit.

    So we now try [X=m /\ Z*Z <= m] as the loop invariant:

    {{ X=m }} ->>                                           (a - OK)
    {{ X=m /\ 0*0 <= m }}
      Z := 0
                 {{ X=m /\ Z*Z <= m }};
      while (Z+1)*(Z+1) <= X do
                 {{ X=m /\ Z*Z<=m /\ (Z+1)*(Z+1)<=X }} ->>  (c - OK)
                 {{ X=m /\ (Z+1)*(Z+1)<=m }}
        Z := Z + 1
                 {{ X=m /\ Z*Z<=m }}
      end
    {{ X=m /\ Z*Z<=m /\ ~((Z+1)*(Z+1)<=X) }} ->>            (b - OK)
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}

    This works, since conditions (a), (b), and (c) are now all
    trivially satisfied.

    Very often, when a variable is used in a loop in a read-only
    fashion (i.e., it is referred to by the program or by the
    specification and it is not changed by the loop), it is necessary
    to record the fact that it doesn't change in the loop invariant. *)

(** **** Exercise: 3 stars, standard, optional (sqrt_formal)

    Translate the above informal decorated program into a formal one
    and prove it correct.

    Hint: The loop invariant here must ensure that Z*Z is consistently
    less than or equal to X. *)

(* DONE: fill in the assertions *)
Definition sqrt_dec (m:nat) : decorated :=
  <{
    {{ X=m }} ->>
    {{ X=m }}
      Z := 0
                    {{ X=m /\ Z*Z <= m }};
      while ((Z+1)*(Z+1) <= X) do
                    {{ X=m /\ Z*Z<=m /\ (Z+1)*(Z+1)<=X  }} ->>
                    {{ X=m /\ (Z+1)*(Z+1)<=m }}
        Z := Z + 1
                    {{ X=m /\ Z*Z<=m }}
      end
    {{ X=m /\ Z*Z<=m /\ ~((Z+1)*(Z+1)<=X) }} ->>
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
  }>.

Theorem sqrt_correct : forall m,
  outer_triple_valid (sqrt_dec m).
Proof. verify. Qed.



(* ################################################################# *)
(* EXERCISE 12 (3 points):  Consider the following triple:        
                                                                   
       {{ X = m }}
         while 2 <= X do
           X := X - 2   !!   X := X+2
         end
       {{ X = parity m }}

    The [parity] function used in the specification is defined in
    Coq as follows: *)   

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

(* The goal of this exercise is to write a corresponding decorated program
   and prove it is correct. The program should be written in definition [parity_dec_nondet]
   and the theorem to prove is [parity_outer_triple_valid_nondet]. The following properties
   of parity may be useful (they might not be needed and, if you want, you can define
   different properties, as long as you prove them.) *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - destruct x.
    + lia.
    + inversion H; subst; simpl.
      * reflexivity.
      * rewrite sub_0_r. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity x = x.
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - destruct x.
    + reflexivity.
    + lia.
Qed.

Lemma parity_plus_2 : forall x,
  parity (x + 2) = parity x.
Proof.
  induction x; intros; simpl.
  - reflexivity.
  - replace (x+2) with (S ( S x)) in *; simpl in *; try lia.
Qed.


Definition parity_dec_nondet (m:nat) : decorated :=
(* DONE: write a decorated version of the program shown above. The pre and post-conditions
should not be changed. Note that the code below does
not typecheck until you decorate it correctly. *)
<{
  {{ X = m }}->>
  {{ ap parity X = parity m }}
    while 2 <= X do
    {{ ap parity X = parity m /\ 2 <= X }} ->>
    {{ ap parity (X-2) = parity m }}
      X := X - 2
      {{ ap parity X = parity m }}
      !!
      X := X + 2
      {{ ap parity X = parity m }}
    end
  {{ ap parity X = parity m /\ ~(2 <= X) }} ->>
  {{ X = parity m }} }>.


Theorem parity_outer_triple_valid_nondet : forall m,
  outer_triple_valid (parity_dec_nondet m).
Proof. 
  verify.
  - destruct (st X) eqn:Heq.
    -- simpl. discriminate.
    -- simpl. destruct n.
       --- discriminate.
       --- destruct n.
           ---- reflexivity.
           ---- lia.
  - destruct (st X) eqn:Heq.
    -- simpl. try rewrite <- Heq. lia.
    -- simpl. destruct n.
       --- lia.
       --- destruct n.
         ---- lia.
         ---- lia.
  - destruct (st X) eqn:Heq.
    -- simpl. try rewrite <- Heq. lia.
    -- simpl. destruct n.
       --- lia.
       --- destruct n.
         ---- simpl. assumption.
         ---- simpl. destruct n.
           ----- assumption.
           ----- assumption.
  - destruct (st X) eqn:Heq.
    -- simpl. try rewrite <- Heq. lia.
    -- simpl. destruct n.
      --- lia.
      --- destruct n.
        ---- simpl. assumption.
        ---- destruct n.
          ----- simpl. assumption.
          ----- simpl. simpl in H. rewrite <- H. apply parity_plus_2.
  - destruct (st X) eqn:Heq.
    -- simpl. try rewrite <- Heq. rewrite Heq. simpl in H. apply H.
    -- simpl. destruct n.
      --- simpl in H. apply H.
      --- destruct n.
       ---- simpl. simpl in H. rewrite <- H. lia.
        ---- destruct n.
          ----- simpl. rewrite <- H. lia.
          ----- simpl. simpl in H. rewrite <- H. lia.
Qed.

End DCom.

End SecondProject.
