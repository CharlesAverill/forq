From Stdlib Require Import NArith List.

From Forq Require Import Syntax State ProgramSemantics MachineModel.
From Forq.Words Require Import Word.

Module Hoare (syntax : WordSyntax) 
             (ST : StateType syntax) 
             (semantics : WordSemantics syntax ST) 
             (model : MachineModel).

Module PS := SmallStep syntax ST semantics model.
Import PS.

Definition Assertion : Type := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Coercion assert_of_Prop : Sortclass >-> Assertion.
Add Printing Coercion assert_of_Prop.
Arguments assert_of_Prop /.
Add Printing Coercion assert_of_Prop.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.

Definition AssertionN : Type := state -> N.
Definition AssertionN_of_N (n : N) : AssertionN :=
  fun _ => n.
Coercion AssertionN_of_N : N >-> AssertionN.
Notation mkAssertN a := (a%assertion : AssertionN).

Definition AssertionMem : Type := state -> memT.
Definition AssertionMem_of_memT (m : memT) : AssertionMem :=
  fun _ => m.
Coercion AssertionMem_of_memT : memT >-> AssertionMem.
Notation mkAssertMem m := (m%assertion : AssertionMem).

Definition AssertionStack : Type := state -> stackT.
Definition AssertionStack_of_stackT (l : stackT) : AssertionStack :=
  fun _ => l.
Coercion AssertionStack_of_stackT : stackT >-> AssertionStack.
Notation mkAssertStack l := (l%assertion : AssertionStack).

Definition AssertionDict : Type := state -> dictT.
Definition AssertionDict_of_dictT (d : dictT) : AssertionDict :=
  fun _ => d.
Notation mkAssertDict d := (d%assertion : AssertionDict).

(* Memory access *)
Notation "@@ a" := (fun st => st.(mem) a) (at level 50) : assertion_scope.
(* Stack access *)
Notation "'.S'" := (fun st => st.(stack)) (at level 65) : assertion_scope.
(* Dictionary access *)
Notation "'WORDS' w" := (fun st => st.(dict) w) (at level 65) : assertion_scope.

(* Notations for N (mostly for reasoning about memory) *)
Notation "a = b" := (fun st => mkAssertN a st = mkAssertN b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAssertN a st <> mkAssertN b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAssertN a st <= mkAssertN b st) : assertion_scope.
Notation "a < b" := (fun st => mkAssertN a st < mkAssertN b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAssertN a st >= mkAssertN b st) : assertion_scope.
Notation "a > b" := (fun st => mkAssertN a st > mkAssertN b st) : assertion_scope.
Notation "a + b" := (fun st => mkAssertN a st + mkAssertN b st) : assertion_scope.
Notation "a - b" := (fun st => mkAssertN a st - mkAssertN b st) : assertion_scope.
Notation "a * b" := (fun st => mkAssertN a st * mkAssertN b st) : assertion_scope.

(* Notations for lists (mostly for reasoning about stack) *)
Notation "a [=] b" := (fun st => mkAssertStack a st = mkAssertStack b st)
  (at level 70, no associativity) : assertion_scope.
Notation "a [<>] b" := (fun st => mkAssertStack a st <> mkAssertStack b st)
  (at level 70, no associativity) : assertion_scope.
Notation "a [::] b" := (fun st => a :: (mkAssertStack b st))
  (at level 50, left associativity) : assertion_scope.
Notation "a [++] b" := (fun st => (mkAssertStack a st) ++ (mkAssertStack b st))
  (at level 50, left associativity) : assertion_scope.

Definition valid_hoare_triple
           (P : Assertion) (p : program) (Q : Assertion) : Prop :=
  forall st st',
     pmstep st p st' ->
     P st  ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 90)
    : hoare_spec_scope.

Theorem hoare_app : forall P Q R t1 t2,
  {{P}} t1 {{Q}} ->
  {{Q}} t2 {{R}} ->
  {{P}} t1 ++ t2 {{R}}.
Proof.
  intros. unfold valid_hoare_triple in *. intros.
  eapply pmstep_app_backward in H1.
  destruct H1 as (s2 & Stept1 & Stept2).
  eapply H0.
    eassumption.
  eapply H.
    eassumption.
  assumption.
Qed.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros. intros st st' _ _. apply H. 
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros. intros st st' _ contra. exfalso. now apply (H st).
Qed.

Definition assertion_sub_stack (stack' : stackT) (P:Assertion) : Assertion :=
  fun (st : state) =>
    P {| stack := stack'; mem := st.(mem); dict := st.(dict) |}.
Notation "P '[.S' := st ]" := (assertion_sub_stack st P)
  (at level 10) : hoare_spec_scope.
Definition assertion_push_stack (val : AssertionN) (P : Assertion) : Assertion :=
  fun (st : state) =>
    P {| stack := (val st) :: st.(stack); mem := st.(mem); dict := st.(dict) |}.
Notation "P '[.S' :: v ]" := (assertion_push_stack (mkAssertN v) P)
  (at level 10) : hoare_spec_scope.

Definition assertion_sub_mem (a : addr) (v : N) (P:Assertion) : Assertion :=
  fun (st : state) =>
    P {| stack := st.(stack); mem := update st.(mem) a v; dict := st.(dict) |}.
Notation "P '[@' a := v ]" := (assertion_sub_mem a v P)
  (at level 10) : hoare_spec_scope.

Definition assertion_sub_dict (a : addr) (p : program) (P:Assertion) : Assertion :=
  fun (st : state) =>
    P {| stack := st.(stack); mem := st.(mem); dict := update st.(dict) a p |}.
Notation "P '[WORDS' a := p ]" := (assertion_sub_dict a p P)
  (at level 10) : hoare_spec_scope.

End Hoare.