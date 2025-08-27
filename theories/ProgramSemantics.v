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
End SmallStep.