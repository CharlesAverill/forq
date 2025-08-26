From Stdlib Require Import List.
Import ListNotations.

From Frocq Require Import Syntax.
From Frocq Require Import Result.
From Frocq.Words Require Import Word.

Module SmallStep (syntax : WordSyntax) (semantics : WordSemantics syntax).
  Export syntax semantics.

  Inductive pmstep : state -> program -> state -> Prop :=
  | PMStepRefl : forall s prog,
      pmstep s prog s
  | PMStepMulti : forall wrd p p' s1 s2 s3,
      cstep s1 wrd (Ok (s2, p')) ->
      pmstep s2 (p' ++ p) s3 ->
      pmstep s1 (wrd :: p) s3.
End SmallStep.