From Forq Require Import Auto.
From Forq.Words Require Import Core.

Module ST := State CoreSyntax.
Module SMX := CoreSemantics ST.

Module Auto := Automation CoreSyntax ST SMX MM8.
Import Auto.

Definition loadstore (addr : word) (val : word) : program := 
  [addr; val; Store; addr; addr; Fetch; Store].

Theorem loadstore_correct : forall (addr val : N) mem dict,
  mem_well_typed mem ->
  val < 2^w ->
  pmstep 
    {| stack := []; mem := mem; dict := dict |}
    (loadstore addr val)
    {| stack := []; mem := mem[addr := val]; dict := dict |}.
Proof.
  intros. unfold loadstore.
  eapply PMStepMulti.
    constructor.
    now cbv [mem].
  simpl. eapply PMStepMulti.
    constructor.
    now cbv [mem].
  simpl. eapply PMStepMulti.
    constructor. reflexivity.
    cbv [mem]. now apply mem_well_typed_update.
  simpl. eapply PMStepMulti.
    constructor.
    cbv [mem]. now apply mem_well_typed_update.
  simpl. eapply PMStepMulti.
    constructor.
    cbv [mem]. now apply mem_well_typed_update.
  simpl. eapply PMStepMulti.
    constructor. reflexivity.
    cbv [mem]. now apply mem_well_typed_update.
  simpl. eapply PMStepMulti.
    constructor. reflexivity.
    cbv [mem]. apply mem_well_typed_update.
      now apply mem_well_typed_update.
      now rewrite update_eq.
  simpl. rewrite update_eq. rewrite update_shadow. apply PMStepRefl.
Qed.

Theorem loadstore_correct' : forall (addr val : N) mem dict,
  mem_well_typed mem ->
  val < 2^w ->
  pmstep 
    {| stack := []; mem := mem; dict := dict |}
    (loadstore addr val)
    {| stack := []; mem := mem[addr := val]; dict := dict |}.
Proof.
  intros. unfold loadstore.
  (* store *)
  step (). step (). step ().
  (* fetch *) 
  step (). step (). step ().
  (* store *)
  step ().
Qed.