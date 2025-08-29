From Stdlib Require Import NArith.
From Stdlib Require Import List.
Import ListNotations.
From Ltac2 Require Import Ltac2.

From Forq.ProofRules Require Import Hoare.
From Forq.Words Require Import Word Core.
From Forq Require Import Syntax State MachineModel Tactics.

Module CoreHoare (ST : StateType CoreSyntax) 
                 (model : MachineModel).
Module SMX := CoreSemantics ST.
Module H := Hoare CoreSyntax ST SMX model.
Export H.
Import ST.
Open Scope hoare_spec_scope.

Theorem hoare_literal : forall P (n : N),
  {{ P[.S :: n] }} [Literal n] {{ P }}.
Proof.
  intros. unfold valid_hoare_triple. intros.
  inv H. inv [WordStep PrependProg].
  apply H0.
Qed.

Theorem hoare_fetch : forall P (addr : addr) tl,
  {{ fun st =>
      st.(stack) = addr :: tl /\
      P {|stack := st.(mem) addr :: tl; mem := st.(mem); dict := st.(dict) |}
  }} [Fetch] {{ P }}.
Proof.
  unfold valid_hoare_triple. intros P addr tl st st' Step (StackEq & PPost).
  inv Step. inv [WordStep PrependProg StackEq]. assumption.
Qed.

Theorem hoare_store : forall P (addr : addr) (val : N) tl,
  {{ fun st =>
      st.(stack) = val :: addr :: tl /\
      P {|stack := tl; mem := update st.(mem) addr val; dict := st.(dict) |}
  }} [Store] {{ P }}.
Proof.
  unfold valid_hoare_triple. intros P addr val tl st st' Step (StackEq & PPost).
  inv Step. inv [WordStep PrependProg StackEq]. assumption.
Qed.

End CoreHoare.