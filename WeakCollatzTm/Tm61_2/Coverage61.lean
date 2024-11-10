import WeakCollatzTm.Tm61_2.Basic
import WeakCollatzTm.Tm61_2.TuringMachine61
import Init.Data.List.Basic

set_option maxHeartbeats 0

open Tm61_2

open Lean Meta Elab Tactic Std Term TmState

unsafe def foo (cfg : Cfg) (unvisited : List (TmState × Γ)): IO Unit :=
do
  let unvisited <- pure (List.removeAll unvisited [⟨cfg.q, cfg.Tape.head⟩])
  IO.println s!"{unvisited}"
  match (step machine cfg) with
  | some cfg => IO.println s!"{cfg}"
                foo cfg unvisited
  | none => IO.println s!"halt"


unsafe def main : List String → IO Unit
| _ => foo (init []) ([
  cp_stage_6 ,
  cp_twice_stage_5 ,
  divide_2_stage_3 ,
  init_pointer_stage_X0 ,
  cp_stage_2 ,
  finished_stage_2 ,
  check_1 ,
  clean_stage_2_X0 ,
  divide_2_stage_1 ,
  clean_stage_2_X1 ,
  cp_twice_stage_3 ,
  odd ,
  pre_check_1 ,
  update_p1 ,
  finished_stage_1 ,
  cp_stage_4 ,
  cp_stage_3 ,
  finished_stage ,
  init_pointer_stage_4 ,
  goto_input_0X ,
  cp_stage_5 ,
  divide_2_stage_5 ,
  divide_2_stage_6 ,
  clean_stage_1 ,
  update_p1_stage_2 ,
  continue_collatz_stage_1_0X ,
  finished_stage_X0 ,
  finished_stage_X1 ,
  init_pointer_stage_2 ,
  init_pointer_stage_1 ,
  check_1_1X ,
  continue_collatz_stage_1 ,
  update_p2_stage_2 ,
  cp_twice_stage_2 ,
  clean_stage_4 ,
  divide_2_stage_2 ,
  continue_collatz_stage_1_1X ,
  update_p1_stage_1 ,
  cp_twice_stage_1 ,
  init_pointer_stage_5 ,
  skip_input ,
  update_visited_stage_2 ,
  cp_twice_stage_7 ,
  pre_goto_input ,
  clean_stage_3 ,
  cp_twice_stage_4 ,
  update_p1_X1 ,
  even ,
  update_p1_stage_3 ,
  goto_input_1X ,
  cp_twice_stage_6 ,
  init_pointer_stage_X1 ,
  update_p1_X0 ,
  continue_collatz_stage_2 ,
  cp_stage_1 ,
  goto_input ,
  divide_2_stage_4 ,
  update_p2_stage_1 ,
  update_visited_stage_1 ,
  check_1_0X ,
  clean_stage_2 ,
  unreachable ,
  ].map (fun q => [⟨q, Γ.zero⟩, ⟨q, Γ.one⟩])).flatten
