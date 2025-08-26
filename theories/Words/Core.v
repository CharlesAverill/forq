From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import NArith.
Open Scope N_scope.

From Frocq Require Import Result.
From Frocq Require Import Syntax.
From Frocq Require Import State.
From Frocq.Words Require Import Word.

Module CoreSyntax <: WordSyntax.
  Inductive CoreWord : Set := Fetch | Store | Exec.
  Definition word : Type := CoreWord.

  Definition program := list word.
End CoreSyntax.

Module CoreSemantics <: (WordSemantics CoreSyntax).
  Module St := State CoreSyntax.
  Export St CoreSyntax.

  Inductive step : state -> CoreWord -> result (state * program) -> Prop :=
    (* fetch *)
    | StepFetchOk : forall (s : state) (addr : addr) (st : list N),
        s.(stack) = addr :: st ->
        step s Fetch
          (Ok ({|stack := s.(mem) addr :: st; 
                mem := s.(mem); dict := s.(dict)|}, []))
    | StepFetchUnderflow : forall (s : state),
        s.(stack) = [] -> step s Fetch (Error "fetch: stack underflow")
    (* store *)
    | StepStoreOk : forall (s : state) (val : N) (addr : addr) (st : list N),
        s.(stack) = val :: addr :: st ->
        step s Store
          (Ok ({|stack := st; mem := update s.(mem) addr val; 
                dict := s.(dict)|}, []))
    | StepStoreUnderflow : forall (s : state),
        s.(stack) = [] \/ (exists x, s.(stack) = [x]) -> 
        step s Store (Error "store: stack underflow")
  .

  Definition cstep := step.
End CoreSemantics.