From Frocq Require Import Syntax.
From Frocq Require Import State.
From Frocq Require Import Result.

Module Type WordSemantics (syntax : WordSyntax).
  Module St := State syntax.
  Export St syntax.

  Parameter cstep : state -> word -> result (state * program) -> Prop.
End WordSemantics.