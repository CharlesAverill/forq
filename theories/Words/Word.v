From Forq Require Import Result Syntax State MachineModel.

Module Type WordSemantics (syntax : WordSyntax) (ST : StateType syntax).
  Parameter step : ST.state -> syntax.word -> result (ST.state * syntax.program) -> Prop.
End WordSemantics.