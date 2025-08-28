From Stdlib Require Import NArith.
Open Scope N.
From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import FunctionalExtensionality.

From Forq Require Import Syntax.

Module Type StateType (syntax : WordSyntax).
  Definition stackT : Type := list N.
  Definition memT : Type := addr -> N.
  Definition dictT : Type := addr -> syntax.program.
  Record state : Type := {
    stack : stackT;
    mem : memT;
    dict : dictT
  }.
End StateType.

Module State (syntax : WordSyntax) <: StateType syntax.
  Definition stackT : Type := list N.
  Definition memT : Type := addr -> N.
  Definition dictT : Type := addr -> syntax.program.

  Record state : Type := {
    stack : stackT;                 (* data stack *)
    mem : memT;                (* memory function *)
    dict : dictT   (* word dictionary *)
  }.

  Definition empty_mem : (addr -> N) :=
    fun _ => 0.

  Definition empty_dict : (addr -> syntax.program) :=
    fun _ => [].
End State.

Definition update {X : Type} (mem : addr -> X) (key : addr) (val : X) : (addr -> X) :=
  fun key' => if key' =? key then val else mem key'.
Notation "m [ k := v ]" := (update m k v).

Definition update_eq : forall {X : Type} mem key (val : X),
  mem [key := val] key = val.
Proof.
  intros. unfold update. now rewrite N.eqb_refl.
Qed.

Definition update_neq : forall {X : Type} mem key1 key2 (val : X),
  key1 <> key2 ->
  mem [key1 := val] key2 = mem key2.
Proof.
  intros. unfold update.
  apply not_eq_sym in H.
  apply N.eqb_neq in H. now rewrite H.
Qed.

Definition update_shadow : forall {X : Type} mem key (val val' : X),
  mem [key := val] [key := val'] = mem [key := val'].
Proof.
  intros. unfold update. apply functional_extensionality. intros.
  now destruct (N.eqb x key).
Qed.