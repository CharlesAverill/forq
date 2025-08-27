From Stdlib Require Import NArith.
From Stdlib Require Import String.
From Stdlib Require Import List.

Module Type WordSyntax.
  Parameter word : Type.

  Definition program := list word.
End WordSyntax.

Definition addr : Type := N.
Definition ident : Type := string.