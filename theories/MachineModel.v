From Stdlib Require Import NArith.

From Forq Require Import Syntax State.

Module Type MachineModel (syntax : WordSyntax).
  Parameter w : N.

  Definition mem_well_typed (mem : addr -> N) : Prop :=
    forall (a : addr), mem a < 2^w.
End MachineModel.

Module MM8 (syntax : WordSyntax) <: MachineModel syntax.
  Definition w := 8.
  Definition mem_well_typed (mem : addr -> N) : Prop :=
    forall (a : addr), mem a < 2^w.
End MM8.

Module MM16 (syntax : WordSyntax) <: MachineModel syntax.
  Definition w := 16.
  Definition mem_well_typed (mem : addr -> N) : Prop :=
    forall (a : addr), mem a < 2^w.
End MM16.

Module MM32 (syntax : WordSyntax) <: MachineModel syntax.
  Definition w := 32.
  Definition mem_well_typed (mem : addr -> N) : Prop :=
    forall (a : addr), mem a < 2^w.
End MM32.

Module MM64 (syntax : WordSyntax) <: MachineModel syntax.
  Definition w := 64.
  Definition mem_well_typed (mem : addr -> N) : Prop :=
    forall (a : addr), mem a < 2^w.
End MM64.