From Ltac2 Require Import Ltac2.

Ltac2 rec inv_list (hs : ident list) :=
  match hs with
  | [] => ()
  | h :: hs' =>
      ltac1:(h |- let h' := fresh h in
        rename h into h'; inversion h'; clear h'; subst) (Ltac1.of_ident h);
      inv_list hs'
  end.

Ltac2 Notation "inv" "[" hs(list1(ident)) "]" :=
  inv_list hs.
Ltac2 Notation "inv" hs(ident) :=
  inv_list [hs].

