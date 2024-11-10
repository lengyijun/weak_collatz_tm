-- inspired by https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine.lean
import Mathlib.Computability.TuringMachine
import Mathlib.Tactic.Ring.RingNF
import WeakCollatzTm.Format
import WeakCollatzTm.Tm61_2.Basic
import WeakCollatzTm.Tm61_2.ListBlank

namespace Tm61_2

inductive TmState where
 | cp_stage_6 : TmState
 | cp_twice_stage_5 : TmState
 | divide_2_stage_3 : TmState
 | init_pointer_stage_X0 : TmState
 | cp_stage_2 : TmState
 | finished_stage_2 : TmState
 | check_1 : TmState
 | clean_stage_2_X0 : TmState
 | divide_2_stage_1 : TmState
 | clean_stage_2_X1 : TmState
 | cp_twice_stage_3 : TmState
 | odd : TmState
 | pre_check_1 : TmState
 | update_p1 : TmState
 | finished_stage_1 : TmState
 | cp_stage_4 : TmState
 | cp_stage_3 : TmState
 | finished_stage : TmState
 | init_pointer_stage_4 : TmState
 | goto_input_0X : TmState
 | cp_stage_5 : TmState
 | divide_2_stage_5 : TmState
 | divide_2_stage_6 : TmState
 | clean_stage_1 : TmState
 | update_p1_stage_2 : TmState
 | continue_collatz_stage_1_0X : TmState
 | finished_stage_X0 : TmState
 | finished_stage_X1 : TmState
 | init_pointer_stage_2 : TmState
 | init_pointer_stage_1 : TmState
 | check_1_1X : TmState
 | continue_collatz_stage_1 : TmState
 | update_p2_stage_2 : TmState
 | cp_twice_stage_2 : TmState
 | clean_stage_4 : TmState
 | divide_2_stage_2 : TmState
 | continue_collatz_stage_1_1X : TmState
 | update_p1_stage_1 : TmState
 | cp_twice_stage_1 : TmState
 | init_pointer_stage_5 : TmState
 | skip_input : TmState
 | update_visited_stage_2 : TmState
 | cp_twice_stage_7 : TmState
 | pre_goto_input : TmState
 | clean_stage_3 : TmState
 | cp_twice_stage_4 : TmState
 | update_p1_X1 : TmState
 | even : TmState
 | update_p1_stage_3 : TmState
 | goto_input_1X : TmState
 | cp_twice_stage_6 : TmState
 | init_pointer_stage_X1 : TmState
 | update_p1_X0 : TmState
 | continue_collatz_stage_2 : TmState
 | cp_stage_1 : TmState
 | goto_input : TmState
 | divide_2_stage_4 : TmState
 | update_p2_stage_1 : TmState
 | update_visited_stage_1 : TmState
 | check_1_0X : TmState
 | clean_stage_2 : TmState
 | unreachable : TmState
deriving BEq


open Lean Meta Elab Tactic Std Term TmState

def TmState.toString : TmState → String
| init_pointer_stage_1 => s!"       init_pointer_stage_1"
| clean_stage_2_X0 => s!"           clean_stage_2_X0"
| cp_twice_stage_4 => s!"           cp_twice_stage_4"
| cp_twice_stage_7 => s!"           cp_twice_stage_7"
| divide_2_stage_5 => s!"           divide_2_stage_5"
| finished_stage_X0 => s!"          finished_stage_X0"
| update_visited_stage_1 => s!"     update_visited_stage_1"
| finished_stage => s!"             finished_stage"
| even => s!"                       even"
| cp_stage_1 => s!"                 cp_stage_1"
| continue_collatz_stage_2 => s!"   continue_collatz_stage_2"
| divide_2_stage_4 => s!"           divide_2_stage_4"
| init_pointer_stage_X1 => s!"      init_pointer_stage_X1"
| init_pointer_stage_4 => s!"       init_pointer_stage_4"
| update_p2_stage_2 => s!"          update_p2_stage_2"
| finished_stage_1 => s!"           finished_stage_1"
| init_pointer_stage_X0 => s!"      init_pointer_stage_X0"
| pre_check_1 => s!"                pre_check_1"
| divide_2_stage_1 => s!"           divide_2_stage_1"
| update_p2_stage_1 => s!"          update_p2_stage_1"
| cp_stage_6 => s!"                 cp_stage_6"
| cp_twice_stage_5 => s!"           cp_twice_stage_5"
| clean_stage_2 => s!"              clean_stage_2"
| divide_2_stage_6 => s!"           divide_2_stage_6"
| clean_stage_3 => s!"              clean_stage_3"
| divide_2_stage_3 => s!"           divide_2_stage_3"
| clean_stage_2_X1 => s!"           clean_stage_2_X1"
| update_p1_X1 => s!"               update_p1_X1"
| cp_twice_stage_3 => s!"           cp_twice_stage_3"
| init_pointer_stage_2 => s!"       init_pointer_stage_2"
| goto_input_1X => s!"              goto_input_1X"
| continue_collatz_stage_1 => s!"   continue_collatz_stage_1"
| clean_stage_1 => s!"              clean_stage_1"
| update_p1_stage_1 => s!"          update_p1_stage_1"
| cp_stage_2 => s!"                 cp_stage_2"
| cp_stage_5 => s!"                 cp_stage_5"
| cp_twice_stage_2 => s!"           cp_twice_stage_2"
| odd => s!"                        odd"
| goto_input => s!"                 goto_input"
| update_p1_stage_2 => s!"          update_p1_stage_2"
| check_1_1X => s!"                 check_1_1X"
| check_1_0X => s!"                 check_1_0X"
| cp_twice_stage_6 => s!"           cp_twice_stage_6"
| cp_stage_4 => s!"                 cp_stage_4"
| update_p1_stage_3 => s!"          update_p1_stage_3"
| cp_stage_3 => s!"                 cp_stage_3"
| finished_stage_2 => s!"           finished_stage_2"
| continue_collatz_stage_1_0X => s!"continue_collatz_stage_1_0X"
| clean_stage_4 => s!"              clean_stage_4"
| divide_2_stage_2 => s!"           divide_2_stage_2"
| cp_twice_stage_1 => s!"           cp_twice_stage_1"
| continue_collatz_stage_1_1X => s!"continue_collatz_stage_1_1X"
| check_1 => s!"                    check_1"
| pre_goto_input => s!"             pre_goto_input"
| skip_input => s!"                 skip_input"
| finished_stage_X1 => s!"          finished_stage_X1"
| update_visited_stage_2 => s!"     update_visited_stage_2"
| update_p1 => s!"                  update_p1"
| update_p1_X0 => s!"               update_p1_X0"
| init_pointer_stage_5 => s!"       init_pointer_stage_5"
| goto_input_0X => s!"              goto_input_0X"
| unreachable => s!"              unreachable"


instance : ToString TmState where
  toString := TmState.toString

def Machine := TmState → Γ → Option (TmState × Stmt)

structure Cfg where
  /-- The current machine state. -/
  q : TmState
  /-- The current state of the tape: current symbol, left and right parts. -/
  Tape : Turing.Tape Γ


instance : ToString Cfg where
  toString := fun ⟨q, ⟨head, l, r⟩⟩ ↦
    let l : String := join ((to_list_rev l).map ToString.toString)
    let r : String := join ((to_list r).map ToString.toString)
    let s : String := if l == "" then s!"[{head}]{r}"
                                 else s!" {l}[{head}]{r}"
    s!"{q}   {s}"

/-- The initial configuration. -/
def init (l : List Γ) : Cfg := ⟨cp_stage_4, Turing.Tape.mk₁ l⟩

/-- Execution semantics of the Turing machine. -/
def step (M : Machine) : Cfg → Option Cfg :=
  fun ⟨q, T⟩ ↦ (M q T.1).map fun ⟨q', a⟩ ↦ ⟨q', (T.write a.write).move a.move⟩


def machine : Machine
| cp_stage_1, Γ.zero => some ⟨cp_stage_2, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_stage_1, Γ.one => some ⟨cp_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_stage_2, Γ.zero => some ⟨even, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_stage_2, Γ.one => some ⟨cp_stage_3, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_stage_3, Γ.zero => some ⟨cp_stage_4, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_stage_3, Γ.one => some ⟨cp_stage_3, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_stage_4, Γ.zero => some ⟨cp_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_stage_4, Γ.one => some ⟨cp_stage_4, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_stage_5, Γ.zero => some ⟨cp_stage_6, ⟨Turing.Dir.left, Γ.zero⟩⟩
| cp_stage_5, Γ.one => some ⟨cp_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_stage_6, Γ.zero => some ⟨cp_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_stage_6, Γ.one => some ⟨cp_stage_6, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_twice_stage_1, Γ.zero => some ⟨cp_twice_stage_2, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_twice_stage_1, Γ.one => some ⟨cp_twice_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_twice_stage_2, Γ.zero => some ⟨update_visited_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_2, Γ.one => some ⟨cp_twice_stage_3, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_twice_stage_3, Γ.zero => some ⟨cp_twice_stage_4, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_twice_stage_3, Γ.one => some ⟨cp_twice_stage_3, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_4, Γ.zero => some ⟨cp_twice_stage_7, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_4, Γ.one => some ⟨cp_twice_stage_4, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_7, Γ.zero => some ⟨cp_twice_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_twice_stage_7, Γ.one => some ⟨unreachable, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_twice_stage_5, Γ.zero => some ⟨cp_twice_stage_6, ⟨Turing.Dir.left, Γ.zero⟩⟩
| cp_twice_stage_5, Γ.one => some ⟨cp_twice_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_twice_stage_6, Γ.zero => some ⟨cp_twice_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_6, Γ.one => some ⟨cp_twice_stage_6, ⟨Turing.Dir.left, Γ.one⟩⟩
| divide_2_stage_1, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| divide_2_stage_1, Γ.one => some ⟨divide_2_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| divide_2_stage_2, Γ.zero => some ⟨divide_2_stage_3, ⟨Turing.Dir.right, Γ.zero⟩⟩
| divide_2_stage_2, Γ.one => some ⟨divide_2_stage_2, ⟨Turing.Dir.left, Γ.one⟩⟩
| divide_2_stage_3, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| divide_2_stage_3, Γ.one => some ⟨divide_2_stage_4, ⟨Turing.Dir.right, Γ.zero⟩⟩
| divide_2_stage_4, Γ.zero => some ⟨divide_2_stage_5, ⟨Turing.Dir.left, Γ.zero⟩⟩
| divide_2_stage_4, Γ.one => some ⟨divide_2_stage_4, ⟨Turing.Dir.right, Γ.one⟩⟩
| divide_2_stage_5, Γ.zero => some ⟨init_pointer_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| divide_2_stage_5, Γ.one => some ⟨divide_2_stage_6, ⟨Turing.Dir.left, Γ.zero⟩⟩
| divide_2_stage_6, Γ.zero => some ⟨divide_2_stage_3, ⟨Turing.Dir.right, Γ.one⟩⟩
| divide_2_stage_6, Γ.one => some ⟨divide_2_stage_6, ⟨Turing.Dir.left, Γ.one⟩⟩
| even, Γ.zero => some ⟨divide_2_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| even, Γ.one => some ⟨odd, ⟨Turing.Dir.right, Γ.one⟩⟩
| odd, Γ.zero => some ⟨cp_twice_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| odd, Γ.one => some ⟨even, ⟨Turing.Dir.right, Γ.one⟩⟩
| update_visited_stage_1, Γ.zero => some ⟨update_visited_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_visited_stage_1, Γ.one => some ⟨update_visited_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| update_visited_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_visited_stage_2, Γ.one => some ⟨init_pointer_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| init_pointer_stage_1, Γ.zero => some ⟨init_pointer_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| init_pointer_stage_1, Γ.one => some ⟨init_pointer_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| init_pointer_stage_2, Γ.zero => some ⟨init_pointer_stage_4, ⟨Turing.Dir.left, Γ.zero⟩⟩
| init_pointer_stage_2, Γ.one => some ⟨init_pointer_stage_2, ⟨Turing.Dir.left, Γ.one⟩⟩
| init_pointer_stage_4, Γ.zero => some ⟨init_pointer_stage_5, ⟨Turing.Dir.left, Γ.zero⟩⟩
| init_pointer_stage_4, Γ.one => some ⟨unreachable, ⟨Turing.Dir.left, Γ.one⟩⟩
| init_pointer_stage_5, Γ.zero => some ⟨init_pointer_stage_X0, ⟨Turing.Dir.left, Γ.zero⟩⟩
| init_pointer_stage_5, Γ.one => some ⟨init_pointer_stage_X1, ⟨Turing.Dir.left, Γ.one⟩⟩
| init_pointer_stage_X0, Γ.zero => some ⟨pre_goto_input, ⟨Turing.Dir.right, Γ.zero⟩⟩
| init_pointer_stage_X0, Γ.one => some ⟨pre_goto_input, ⟨Turing.Dir.right, Γ.zero⟩⟩
| pre_goto_input, Γ.zero => some ⟨goto_input, ⟨Turing.Dir.right, Γ.zero⟩⟩
| pre_goto_input, Γ.one => some ⟨goto_input, ⟨Turing.Dir.right, Γ.one⟩⟩
| init_pointer_stage_X1, Γ.zero => some ⟨pre_goto_input, ⟨Turing.Dir.right, Γ.one⟩⟩
| init_pointer_stage_X1, Γ.one => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| goto_input, Γ.zero => some ⟨goto_input_0X, ⟨Turing.Dir.right, Γ.zero⟩⟩
| goto_input, Γ.one => some ⟨goto_input_1X, ⟨Turing.Dir.right, Γ.one⟩⟩
| goto_input_0X, Γ.zero => some ⟨skip_input, ⟨Turing.Dir.right, Γ.zero⟩⟩
| goto_input_0X, Γ.one => some ⟨goto_input, ⟨Turing.Dir.right, Γ.one⟩⟩
| goto_input_1X, Γ.zero => some ⟨goto_input, ⟨Turing.Dir.right, Γ.zero⟩⟩
| goto_input_1X, Γ.one => some ⟨unreachable, ⟨Turing.Dir.right, Γ.one⟩⟩
| skip_input, Γ.zero => some ⟨update_p2_stage_1, ⟨Turing.Dir.right, Γ.zero⟩⟩
| skip_input, Γ.one => some ⟨skip_input, ⟨Turing.Dir.right, Γ.one⟩⟩
| update_p2_stage_1, Γ.zero => some ⟨update_p2_stage_2, ⟨Turing.Dir.left, Γ.one⟩⟩
| update_p2_stage_1, Γ.one => some ⟨update_p2_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| update_p2_stage_2, Γ.zero => some ⟨finished_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_p2_stage_2, Γ.one => some ⟨update_p1_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_p1_stage_1, Γ.zero => some ⟨update_p1_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_p1_stage_1, Γ.one => some ⟨update_p1_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| update_p1_stage_2, Γ.zero => some ⟨update_p1_stage_3, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_p1_stage_2, Γ.one => some ⟨update_p1_stage_2, ⟨Turing.Dir.left, Γ.one⟩⟩
| update_p1_stage_3, Γ.zero => some ⟨update_p1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_p1_stage_3, Γ.one => some ⟨unreachable, ⟨Turing.Dir.left, Γ.one⟩⟩
| update_p1, Γ.zero => some ⟨update_p1_X0, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_p1, Γ.one => some ⟨update_p1_X1, ⟨Turing.Dir.left, Γ.one⟩⟩
| update_p1_X0, Γ.zero => some ⟨init_pointer_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| update_p1_X0, Γ.one => some ⟨update_p1, ⟨Turing.Dir.left, Γ.one⟩⟩
| update_p1_X1, Γ.zero => some ⟨update_p1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_p1_X1, Γ.one => some ⟨init_pointer_stage_5, ⟨Turing.Dir.left, Γ.zero⟩⟩
| finished_stage_1, Γ.zero => some ⟨finished_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| finished_stage_1, Γ.one => some ⟨finished_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| finished_stage_2, Γ.zero => some ⟨finished_stage, ⟨Turing.Dir.left, Γ.zero⟩⟩
| finished_stage_2, Γ.one => some ⟨unreachable, ⟨Turing.Dir.left, Γ.one⟩⟩
| finished_stage, Γ.zero => some ⟨finished_stage_X0, ⟨Turing.Dir.left, Γ.zero⟩⟩
| finished_stage, Γ.one => some ⟨finished_stage_X1, ⟨Turing.Dir.left, Γ.one⟩⟩
| finished_stage_X0, Γ.zero => some ⟨pre_check_1, ⟨Turing.Dir.right, Γ.zero⟩⟩
| finished_stage_X0, Γ.one => some ⟨finished_stage, ⟨Turing.Dir.left, Γ.one⟩⟩
| finished_stage_X1, Γ.zero => some ⟨finished_stage, ⟨Turing.Dir.left, Γ.zero⟩⟩
| finished_stage_X1, Γ.one => none
| pre_check_1, Γ.zero => some ⟨check_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| pre_check_1, Γ.one => some ⟨unreachable, ⟨Turing.Dir.right, Γ.one⟩⟩
| check_1, Γ.zero => some ⟨check_1_0X, ⟨Turing.Dir.right, Γ.zero⟩⟩
| check_1, Γ.one => some ⟨check_1_1X, ⟨Turing.Dir.right, Γ.one⟩⟩
| check_1_0X, Γ.zero => some ⟨clean_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| check_1_0X, Γ.one => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| check_1_1X, Γ.zero => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.zero⟩⟩
| check_1_1X, Γ.one => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| continue_collatz_stage_1, Γ.zero => some ⟨continue_collatz_stage_1_0X, ⟨Turing.Dir.right, Γ.zero⟩⟩
| continue_collatz_stage_1, Γ.one => some ⟨continue_collatz_stage_1_1X, ⟨Turing.Dir.right, Γ.one⟩⟩
| continue_collatz_stage_1_0X, Γ.zero => some ⟨continue_collatz_stage_2, ⟨Turing.Dir.right, Γ.zero⟩⟩
| continue_collatz_stage_1_0X, Γ.one => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| continue_collatz_stage_1_1X, Γ.zero => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.zero⟩⟩
| continue_collatz_stage_1_1X, Γ.one => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| continue_collatz_stage_2, Γ.zero => some ⟨even, ⟨Turing.Dir.right, Γ.zero⟩⟩
| continue_collatz_stage_2, Γ.one => some ⟨continue_collatz_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| clean_stage_1, Γ.zero => some ⟨clean_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| clean_stage_1, Γ.one => some ⟨unreachable, ⟨Turing.Dir.left, Γ.one⟩⟩
| clean_stage_2, Γ.zero => some ⟨clean_stage_2_X0, ⟨Turing.Dir.left, Γ.zero⟩⟩
| clean_stage_2, Γ.one => some ⟨clean_stage_2_X1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| clean_stage_2_X0, Γ.zero => some ⟨clean_stage_3, ⟨Turing.Dir.right, Γ.zero⟩⟩
| clean_stage_2_X0, Γ.one => some ⟨clean_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| clean_stage_2_X1, Γ.zero => some ⟨clean_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| clean_stage_2_X1, Γ.one => some ⟨clean_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| clean_stage_3, Γ.zero => some ⟨clean_stage_3, ⟨Turing.Dir.right, Γ.zero⟩⟩
| clean_stage_3, Γ.one => some ⟨clean_stage_4, ⟨Turing.Dir.right, Γ.one⟩⟩
| clean_stage_4, Γ.zero => some ⟨cp_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| clean_stage_4, Γ.one => some ⟨clean_stage_4, ⟨Turing.Dir.right, Γ.one⟩⟩
| unreachable , _ => none


def nth_cfg : (n : Nat) -> Option Cfg
| 0 => init []
| Nat.succ n => match (nth_cfg n) with
                | none => none
                | some cfg =>  step machine cfg


-- https://leanprover.zulipchat.com/#narrow/channel/430676-lean4/topic/binderIdent.20vs.20Ident/near/402517388
def toBinderIdent (i : Ident) : TSyntax ``binderIdent := Unhygienic.run <|
  withRef i `(binderIdent| $i:ident)

elab "forward" g:ident : tactic => withSynthesize <| withMainContext do
  let some ldecl := (← getLCtx).findFromUserName? g.getId
    | throwErrorAt g m!"Identifier {g} not found"
  match ldecl with
  | LocalDecl.cdecl _ _ _ (Expr.app (Expr.app _ (Expr.app _ arg)) _) _ _ =>
      let argType ← inferType arg
      if ← isDefEq argType (mkConst ``Nat) then
        let arg ← Elab.Term.exprToSyntax arg
        evalTactic (← `(tactic| (
            have h : nth_cfg ($arg + 1) = nth_cfg ($arg + 1) := rfl
            nth_rewrite 2 [nth_cfg] at h
            simp [*, step, Option.map, machine, Turing.Tape.write, Turing.Tape.move] at h
            try simp! [*, -nth_cfg] at h
            try ring_nf at h
            clear $g
            rename_i $(toBinderIdent g)
        )))
      else
        throwError "The first argument of {g} is not a Nat"
  | _ => logInfo m!"please forward on nth_cfg i = some ⟨...⟩"

end Tm61_2

