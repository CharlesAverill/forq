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
    | StepFetchOk : forall (s : state) (addr : addr),
        cstep {|stack := addr :: s.(stack); mem := s.(mem); dict := s.(dict) |} 
            Fetch
          (Ok ({|stack := s.(mem) addr :: s.(stack); 
                mem := s.(mem); dict := s.(dict)|}, []))
    | StepFetchUnderflow : forall (s : state),
        s.(stack) = [] -> cstep s Fetch (Error "fetch: stack underflow")
    (* store *)
    | StepStoreOk : forall (s : state) (val : N) (addr : addr) (st : list N),
        s.(stack) = val :: addr :: st ->
        cstep s Store
          (Ok ({|stack := st; mem := s.(mem)[addr := val]; 
                dict := s.(dict)|}, []))
    | StepStoreUnderflow : forall (s : state),
        s.(stack) = [] \/ (exists x, s.(stack) = [x]) -> 
        cstep s Store (Error "store: stack underflow")
    (* exec *)
    | StepExecOk : forall (s : state) (st : list N) (prog_addr : addr),
        s.(stack) = prog_addr :: st ->
        cstep s Exec (Ok ({|stack := st; mem := s.(mem); dict := s.(dict)|}, 
                          s.(dict) prog_addr))
    | StepExecUnderflow : forall (s : state),
        s.(stack) = [] ->
        cstep s Exec (Error "exec: stack underflow")
  .

  Definition step := cstep.
End CoreSemantics.


