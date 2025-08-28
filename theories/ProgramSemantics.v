From Stdlib Require Import List.
Import ListNotations.

From Forq Require Import Result State Syntax MachineModel.
From Forq.Words Require Import Word.

Module SmallStep (syntax : WordSyntax)
                 (ST : StateType syntax)
                 (semantics : WordSemantics syntax ST) 
                 (model : MachineModel).
Module MM := model syntax.
Export syntax ST semantics MM.

Definition nilprog : program := [].
Inductive pmstep : state -> program -> state -> Prop :=
| PMStepRefl : forall s,
    pmstep s nilprog s
| PMStepMulti : forall wrd p p' s1 s2 s3,
    step s1 wrd (Ok (s2, p')) ->
    mem_well_typed s2.(mem) ->
    pmstep s2 (p' ++ p) s3 ->
    pmstep s1 (wrd :: p) s3.

Theorem pmstep_app_forward : forall p1 p2 s1 s2 s3,
  pmstep s1 p1 s2 ->
  pmstep s2 p2 s3 ->
  pmstep s1 (p1 ++ p2) s3.
Proof.
  intros. revert s3 p2 H0.
  induction H; intros; subst; simpl in *.
    assumption.
  econstructor. eassumption. assumption.
  rewrite app_assoc. apply IHpmstep. assumption.
Qed.

Lemma pmstep_app_backward_gen :
  forall s1 prog s3,
    pmstep s1 prog s3 ->
    forall p1 p2,
      prog = p1 ++ p2 ->
      exists s2, pmstep s1 p1 s2 /\ pmstep s2 p2 s3.
Proof.
  intros s1 prog s3 H. induction H; intros.
    symmetry in H; apply app_eq_nil in H; destruct H; subst.
    eexists. split; constructor.
  destruct p1.
    exists s1. split. constructor. simpl in H2; subst. econstructor.
    eassumption. assumption. apply H1.
  simpl in H2; inversion H2; subst; clear H2.
  specialize (IHpmstep (p' ++ p1) p2).
  rewrite app_assoc in IHpmstep. specialize (IHpmstep eq_refl).
  destruct IHpmstep as (s4 & IHp1 & IHp2).
  eexists. split. econstructor. eassumption. assumption.
  eassumption. assumption.
Qed.

Lemma pmstep_app_backward : forall p1 p2 s1 s3,
  pmstep s1 (p1 ++ p2) s3 ->
  exists s2, pmstep s1 p1 s2 /\ pmstep s2 p2 s3.
Proof.
  intros.
  apply (pmstep_app_backward_gen s1 (p1 ++ p2) s3 H p1 p2 eq_refl).
Qed.

End SmallStep.
