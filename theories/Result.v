From Stdlib Require Export String.

Inductive result (T : Type) : Type :=
  | Ok (t : T)
  | Error (msg : string).
Arguments Ok [T] _.
Arguments Error [T] _.

Definition get_default {T : Type} (r : result T) (default : T) : T :=
  match r with
  | Ok t => t
  | Error _ => default
  end.