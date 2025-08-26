From Stdlib Require Import NArith.
Open Scope N_scope.
From Stdlib Require Import List.
Import ListNotations.

From Forq Require Import Auto.
From Forq.Words Require Import Core.

Module Auto := Automation CoreSyntax CoreSemantics.
Import Auto.

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

Theorem loadstore_ident' : forall addr val dict, 
  pmstep 
    {| stack := [addr; addr]; mem := update empty_mem addr val; dict := dict |}
    loadstore
    {| stack := []; mem := update empty_mem addr val; dict := dict |}.
Proof.
  intros. unfold loadstore. step (). step ().
Qed.