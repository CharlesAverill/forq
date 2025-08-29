From Forq Require Import Auto.
From Forq.Words Require Import Core.
From Forq.ProofRules Require Import Hoare.
From Forq.ProofRules.Words Require Import Core.

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
    constructor.
    cbv [mem]. now apply mem_well_typed_update.
  simpl. eapply PMStepMulti.
    constructor.
    cbv [mem]. now apply mem_well_typed_update.
  simpl. eapply PMStepMulti.
    constructor.
    cbv [mem]. now apply mem_well_typed_update.
  simpl. eapply PMStepMulti.
    constructor.
    cbv [mem]. now apply mem_well_typed_update.
  simpl. eapply PMStepMulti.
    constructor.
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

Module CoreHoare := CoreHoare ST MM8.
Import CoreHoare.

Definition mem_wt : Assertion := fun st => PS.MM.mem_well_typed st.(mem).

Theorem loadstore_correct'' : forall (a val : N),
  {{ mem_wt }} loadstore a val {{ @@a = val }}.
Proof.
  intros. unfold loadstore.
  (* store *)
  eapply hoare_cons. eapply hoare_consequence_pre with
      (Q := fun st => mem_wt st /\ exists tl, st.(stack) = a :: tl).
    apply hoare_literal. intros st H.
    unfold assertion_push_stack, mem_wt. simpl. split. assumption. exists st.(stack).
    reflexivity.
  eapply hoare_cons. eapply hoare_consequence_pre with
      (Q := fun st => mem_wt st /\ exists tl, st.(stack) = val :: a :: tl).
    apply hoare_literal. intros st (WT & t & St).
    unfold assertion_push_stack, mem_wt. simpl. split. assumption. exists t. now rewrite St.
  eapply hoare_cons with (Q := fun st => mem_wt st /\ exists (m : memT), st.(mem) = m[a := val]).
  eapply hoare_consequence_pre. apply hoare_store with (addr := a) (val := val).
    intros st (WT & t & St). split; ltac1:(cycle 1).
    split. unfold mem_wt. simpl. (mem_well_typed_update (mem st) a val).
  apply hoare_consequence_pre with
    (P' := fun st =>
      st.(stack) = val :: a :: nil /\
      mem_wt[@a := val] {|stack := nil; mem := st.(mem)[a := val]; dict := st.(dict)|}).
    apply hoare_store. intros st H. split.