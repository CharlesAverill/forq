From Stdlib Require Import NArith.
From Stdlib Require Import List.
Import ListNotations.

From Forq.ProofRules Require Import Hoare.
From Forq.Words Require Import Word Core.
From Forq Require Import Syntax State MachineModel.

Module CoreHoare (ST : StateType CoreSyntax) 
                 (model : MachineModel).
Module SMX := CoreSemantics ST.
Module H := Hoare CoreSyntax ST SMX model.
Export H.
Import ST.
Open Scope hoare_spec_scope.

Theorem hoare_literal : forall P (n : N),
  {{ P[.S :: n] }} [Literal n] {{ P }}.
Proof.
  intros. unfold valid_hoare_triple. intros.
  inversion H; clear H; subst. rewrite app_nil_r in H7.
  inversion H3; clear H3; subst. inversion H7; clear H7; subst.
  apply H0.
Qed.

Goal forall (s : stackT), {{ .S [=] s }} [Literal 5] {{ .S [=] (5 :: s : stackT) }}.
  unfold valid_hoare_triple. intros.
  inversion H; subst; clear H. inversion H3; subst; clear H3.
  inversion H7; subst; clear H7. simpl. rewrite H0.
  reflexivity.
Qed.

Goal forall addr tl, {{ .S [=] (addr :: tl : stackT) }} [Fetch] {{fun st => st.(stack) = st.(mem) addr :: tl }}.
  unfold valid_hoare_triple. intros.
  inversion H; subst; clear H. destruct st.
  inversion H3; subst; clear H3.
  inversion H7; subst; clear H7. simpl in *.
  replace (mkAssertStack (addr :: tl : stackT) _) with (addr :: tl) in H0 by reflexivity.
  inversion H0; subst; clear H0. reflexivity.
Qed.

Theorem hoare_fetch : forall P (addr : N),
  {{ P[.S :: @@ addr] }} [Fetch] {{ P[.S :: addr] }}.
Proof.
  unfold valid_hoare_triple, assertion_push_stack. intros.
  destruct st, st'. simpl in *.
  replace ((mkAssertN addr) _) with addr by reflexivity.
  destruct stack0. inversion H; inversion H3.
  inversion H; subst; clear H. rewrite app_nil_r in H7.
  inversion H3; subst; clear H3; simpl in *.
  inversion H7; subst; clear H7.
Abort.

End CoreHoare.