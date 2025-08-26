From Stdlib Require Import NArith.
Open Scope N_scope.
From Stdlib Require Import List.
Import ListNotations.

From Frocq Require Import Syntax ProgramSemantics State.
From Frocq.Words Require Import Core.

Module PS := SmallStep CoreSyntax CoreSemantics.
Export PS.

Definition loadstore : program := [Fetch; Store].

Theorem loadstore_ident : forall addr val dict, 
  pmstep 
    {| stack := [addr; addr]; mem := update empty_mem addr val; dict := dict |}
    loadstore
    {| stack := []; mem := update empty_mem addr val; dict := dict |}.
Proof.
  intros. unfold loadstore.
  eapply PMStepMulti.
  - constructor. reflexivity.
  - simpl. rewrite update_eq. eapply PMStepMulti.
    -- constructor. reflexivity.
    -- simpl. rewrite update_shadow. apply PMStepRefl.
Qed.