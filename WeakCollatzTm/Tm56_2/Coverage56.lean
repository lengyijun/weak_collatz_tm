import WeakCollatzTm.Tm56_2.Basic
import WeakCollatzTm.Tm56_2.TuringMachine56
import Init.Data.List.Basic

set_option maxHeartbeats 0

open Tm56_2

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
  cp_twice_stage_6 ,
  even ,
  continue_collatz_stage_1_1X ,
  continue_collatz_stage_2 ,
  update_visited_stage_1 ,
  init_pv_X1 ,
  continue_collatz_stage_1 ,
  cp_twice_stage_3 ,
  goto_input ,
  cp_stage_2 ,
  pre_check_1 ,
  update_visited_stage_2 ,
  check_1 ,
  cp_twice_stage_5 ,
  goto_input_0X ,
  update_pv_X1 ,
  skip_input ,
  reset_visited_X0 ,
  init_pv_stage_2 ,
  cp_stage_4 ,
  update_pv_stage_1 ,
  divide_2_stage_4 ,
  reset_visited ,
  cp_stage_5 ,
  divide_2_stage_5 ,
  cp_stage_1 ,
  init_pv_stage_1 ,
  update_pv_stage_2 ,
  divide_2_stage_6 ,
  divide_2_stage_1 ,
  finished_stage ,
  reset_visited_X1 ,
  update_pc_stage_2 ,
  cp_stage_3 ,
  init_pv_X0 ,
  init_pv_stage_3 ,
  cp_stage_6 ,
  divide_2_stage_3 ,
  init_pv_stage_4 ,
  check_1_0X ,
  continue_collatz_stage_1_0X ,
  goto_input_and_plus_2 ,
  update_pv_X0 ,
  cp_twice_stage_7 ,
  update_pc_stage_1 ,
  cp_twice_stage_1 ,
  finished_stage_1 ,
  finished_X1 ,
  cp_twice_stage_4 ,
  odd ,
  pre_goto_input ,
  plus_2 ,
  cp_twice_stage_2 ,
  finished_X0 ,
  divide_2_stage_2 ,
  update_pv ,
  ].map (fun q => [⟨q, Γ.zero⟩, ⟨q, Γ.one⟩])).flatten
