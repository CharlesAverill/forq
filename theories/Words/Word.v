From Forq Require Import Syntax.
From Forq Require Import State.
From Forq Require Import Result.

Module Type WordSemantics (syntax : WordSyntax).
  Module St := State syntax.
  Export St syntax.

  Parameter cstep : state -> word -> result (state * program) -> Prop.
End WordSemantics.