import WeakCollatzTm.Tm56_2.Basic
import WeakCollatzTm.Tm56_2.TuringMachine56

open Tm56_2

unsafe def foo (cfg : Cfg) : IO Unit :=
match (step machine cfg) with
| some cfg => do
                IO.println s!"{cfg}"
                foo cfg
| none => IO.println s!"halt"


unsafe def main : List String → IO Unit
| _ => foo (init [])

