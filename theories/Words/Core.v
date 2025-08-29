From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import String.
From Stdlib Require Import NArith.
Open Scope N_scope.

From Forq Require Import Result Syntax State MachineModel.
From Forq.Words Require Import Word.

Module CoreSyntax <: WordSyntax.
  Inductive CoreWord : Set :=
    | Literal (n : N)       (* put constant integer onto stack - https://forth-standard.org/standard/core/LITERAL *)
    | Fetch                 (* load from memory address - https://forth-standard.org/standard/core/Fetch *)
    | Store                 (* store to memory address - https://forth-standard.org/standard/core/Store *)
    | Exec                  (* execute program - https://forth-standard.org/standard/core/EXECUTE *)
    .
  Definition word : Type := CoreWord.
  Coercion Literal : N >-> CoreWord.

  Definition program := list word.
End CoreSyntax.
Export CoreSyntax.

Module CoreSemantics (ST : StateType CoreSyntax) <: (WordSemantics CoreSyntax ST).
  Import ST.
  Inductive cstep : state -> CoreWord -> result (state * program) -> Prop :=
    (* literal *)
    | StepLiteralOk : forall (s : state) (n : N),
        cstep s n
          (Ok ({|stack := n :: s.(stack); mem := s.(mem); dict := s.(dict)|}, []))
    (* fetch *)
    | StepFetchOk : forall (addr : addr) (st : stackT) (mem : memT) (dict : dictT),
        cstep {|stack := addr :: st; mem := mem; dict := dict|} 
            Fetch
          (Ok ({|stack := mem addr :: st; mem := mem; dict := dict|}, []))
    | StepFetchUnderflow : forall (mem : memT) (dict : dictT),
        cstep {|stack := []; mem := mem; dict := dict|} Fetch (Error "fetch: stack underflow")
    (* store *)
    | StepStoreOk : forall (val : N) (addr : addr) (st : stackT) (mem : memT) (dict : dictT),
        cstep {|stack := val :: addr :: st; mem := mem; dict := dict|} 
            Store
          (Ok ({|stack := st; mem := mem[addr := val]; dict := dict|}, []))
    | StepStoreUnderflow : forall (s : state),
        (List.length s.(stack) <= 1)%nat -> 
        cstep s Store (Error "store: stack underflow")
    (* exec *)
    | StepExecOk : forall (prog_addr : addr) (st : stackT) (mem : memT) (dict : dictT),
        cstep {|stack := prog_addr :: st; mem := mem; dict := dict|}
            Exec 
          (Ok ({|stack := st; mem := mem; dict := dict|}, dict prog_addr))
    | StepExecUnderflow : forall (mem : memT) (dict : dictT),
        cstep {|stack := []; mem := mem; dict := dict|} Exec (Error "exec: stack underflow")
  .

  Definition step := cstep.
End CoreSemantics.


