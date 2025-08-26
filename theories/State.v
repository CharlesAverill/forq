From Stdlib Require Import NArith.
Open Scope N.
From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import FunctionalExtensionality.

From Forq Require Import Syntax.

Module State (syntax : WordSyntax).
  Export syntax.

  Record state := {
    stack : list N;         (* data stack *)
    mem : addr -> N;        (* memory function *)
    dict : addr -> program (* word dictionary *)
  }.

  Definition empty_mem : (addr -> N) :=
    fun _ => 0.

  Definition empty_dict : (addr -> program) :=
    fun _ => [].
End State.

Definition update (mem : addr -> N) (key : addr) (val : N) : (addr -> N) :=
  fun key' => if key' =? key then val else mem key'.

Definition update_eq : forall mem key val,
  update mem key val key = val.
Proof.
  intros. unfold update. now rewrite N.eqb_refl.
Qed.

Definition update_shadow : forall mem key val val',
  update (update mem key val) key val' = update mem key val'.
Proof.
  intros. unfold update. apply functional_extensionality. intros.
  now destruct (N.eqb x key).
Qed.