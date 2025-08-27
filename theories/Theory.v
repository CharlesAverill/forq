From Stdlib Require Import NArith.
From Forq Require Import Syntax MachineModel State.

Module ForqTheory (syntax : WordSyntax) (MM : MachineModel syntax).
Import MM.

Lemma mem_well_typed_update : forall mem addr val,
  mem_well_typed mem ->
  val < 2^w ->
  mem_well_typed (mem[addr := val]).
Proof.
  intros. unfold mem_well_typed in *.
  intros. destruct (N.eq_dec a addr).
  - subst. rewrite update_eq. assumption.
  - rewrite update_neq by (symmetry; assumption).
    apply H.
Qed.

End ForqTheory.