From Stdlib Require Export NArith Lia.
Open Scope N_scope.
From Stdlib Require Export List.
Export ListNotations.

From Ltac2 Require Export Ltac2 Pattern Message.
Ltac2 msg x := print (of_string x).

From Forq Require Export Syntax Word ProgramSemantics State MachineModel Theory.

Module Automation (syntax : WordSyntax) 
                  (ST : StateType syntax) 
                  (semantics : WordSemantics syntax ST) 
                  (model : MachineModel).

Module PS := SmallStep syntax ST semantics model.
Module TH := ForqTheory syntax PS.MM.
Export PS TH.

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

Ltac2 stop () :=
  match! goal with
  | [|- pmstep ?s1 nil ?s2 ] => 
      if Constr.equal s1 s2 then (
        apply PMStepRefl
      ) else ()
  end.

Ltac solve_wt :=
  cbv [mem];
  match goal with
  | [H: mem_well_typed ?m |- mem_well_typed ?m] =>
      apply H
  | [WT: mem_well_typed ?m1 |- mem_well_typed (?m2 [_ := ?n])] =>
      apply mem_well_typed_update; [solve_wt | lia]
  end.

Ltac2 step () :=
  match! goal with
  | [|- pmstep _ (_ :: _) _ ] =>
      eapply PMStepMulti > [
          now constructor
        | ltac1:(solve_wt)
        |
      ]
  end;
  fsimpl ();
  try (stop ()).

End Automation.