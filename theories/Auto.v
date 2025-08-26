From Stdlib Require Import List.
Import ListNotations.

From Ltac2 Require Export Ltac2 Pattern.

From Forq Require Export Syntax Word ProgramSemantics State.
From Forq.Words Require Import Core.

Module Automation (syntax : WordSyntax) (semantics : WordSemantics syntax).

Module PS := SmallStep syntax semantics.
Export syntax semantics PS.

Ltac2 change2 (lhs : constr) (rhs : constr) :=
  ltac1:(lhs rhs |- change lhs with rhs)
          (Ltac1.of_constr lhs) (Ltac1.of_constr rhs).

Ltac2 fsimpl () :=
  repeat (match! goal with
  | [|- context[[] ++ ?l] ] =>
      ltac1:(l |- change ([] ++ l) with l) (Ltac1.of_constr l)
  | [|- context[update _ ?x _ ?x] ] => rewrite update_eq
  | [|- context[update (update _ ?x _) ?x _ ] ] => rewrite update_shadow
  | [|- context[stack _ ] ] => cbv [stack]
  | [|- context[mem _ ] ] => cbv [mem]
  | [|- context[dict _ ] ] => cbv [dict]
  end).

Ltac2 step () :=
  match! goal with
  | [|- pmstep ?s1 ?p ?s2 ] =>
      eapply PMStepMulti > [
        now constructor
      |]
  end;
  fsimpl ();
  try (match! goal with
  | [|- pmstep ?s _ ?s ] => apply PMStepRefl
  end).

End Automation.