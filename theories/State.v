From Stdlib Require Import NArith.
Open Scope N.
From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import FunctionalExtensionality.

From Forq Require Import Syntax.

Module Type StateType (syntax : WordSyntax).
  Record state : Type := {
    stack : list N;
    mem : addr -> N;
    dict : addr -> syntax.program
  }.
End StateType.

Module State (syntax : WordSyntax) <: StateType syntax.
  Record state : Type := {
    stack : list N;                 (* data stack *)
    mem : addr -> N;                (* memory function *)
    dict : addr -> syntax.program   (* word dictionary *)
  }.

  Definition empty_mem : (addr -> N) :=
    fun _ => 0.

  Definition empty_dict : (addr -> syntax.program) :=
    fun _ => [].
End State.

Definition update (mem : addr -> N) (key : addr) (val : N) : (addr -> N) :=
  fun key' => if key' =? key then val else mem key'.
Notation "m [ k := v ]" := (update m k v).

Definition update_eq : forall mem key val,
  mem [key := val] key = val.
Proof.
  intros. unfold update. now rewrite N.eqb_refl.
Qed.

Definition update_neq : forall mem key1 key2 val,
  key1 <> key2 ->
  mem [key1 := val] key2 = mem key2.
Proof.
  intros. unfold update.
  apply not_eq_sym in H.
  apply N.eqb_neq in H. now rewrite H.
Qed.

Definition update_shadow : forall mem key val val',
  mem [key := val] [key := val'] = mem [key := val'].
Proof.
  intros. unfold update. apply functional_extensionality. intros.
  now destruct (N.eqb x key).
Qed.