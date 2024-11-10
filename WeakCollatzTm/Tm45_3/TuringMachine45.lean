-- inspired by https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine.lean
import Mathlib.Computability.TuringMachine
import Mathlib.Tactic.Ring.RingNF
import WeakCollatzTm.Format
import WeakCollatzTm.Tm45_3.Basic
import WeakCollatzTm.Tm45_3.ListBlank

namespace Tm45_3

inductive TmState where
| cp_twice_stage_5 : TmState
| init_pointer_stage_3 : TmState
| plus_1_stage_2 : TmState
| divide_2_stage_4 : TmState
| cp_stage_5 : TmState
| even : TmState
| cp_twice_stage_1 : TmState
| cp_twice_stage_4 : TmState
| init_pointer_stage_2 : TmState
| origin_0_stage_1 : TmState
| odd : TmState
| origin_0_stage_6 : TmState
| origin_1_stage_1 : TmState
| origin_1_stage_4 : TmState
| bootstrap_stage_1 : TmState
| cp_stage_3 : TmState
| cp_twice_stage_2 : TmState
| origin_1_stage_6 : TmState
| cleanup_visited : TmState
| cp_stage_2 : TmState
| origin_1_stage_7 : TmState
| check_1 : TmState
| update_visited_stage_2 : TmState
| origin_0_stage_4 : TmState
| continue_collatz_stage_1 : TmState
| origin_0_stage_7 : TmState
| cp_twice_stage_3 : TmState
| origin_1_stage_3 : TmState
| origin_1_stage_5 : TmState
| init_pointer_stage_1 : TmState
| origin_0_stage_5 : TmState
| origin_0_stage_2 : TmState
| cp_stage_4 : TmState
| divide_2_stage_2 : TmState
| cp_twice_stage_6 : TmState
| update_visited_stage_1 : TmState
| origin_1_stage_2 : TmState
| continue_collatz_stage_2 : TmState
| divide_2_stage_1 : TmState
| finish_0_stage_1 : TmState
| plus_1_stage_1 : TmState
| finish_0_stage_2 : TmState
| divide_2_stage_3 : TmState
| origin_0_stage_3 : TmState
| cp_stage_1 : TmState
| unreachable : TmState
deriving BEq

open Lean Meta Elab Tactic Std Term TmState

def TmState.toString : TmState → String
| origin_1_stage_3 => s!"        origin_1_stage_3"
| cp_stage_2 => s!"              cp_stage_2"
| finish_0_stage_1 => s!"        finish_0_stage_1"
| origin_1_stage_6 => s!"        origin_1_stage_6"
| check_1 => s!"                 check_1"
| continue_collatz_stage_1 => s!"continue_collatz_stage_1"
| plus_1_stage_1 => s!"          plus_1_stage_1"
| cleanup_visited => s!"         cleanup_visited"
| finish_0_stage_2 => s!"        finish_0_stage_2"
| origin_1_stage_5 => s!"        origin_1_stage_5"
| origin_0_stage_4 => s!"        origin_0_stage_4"
| plus_1_stage_2 => s!"          plus_1_stage_2"
| divide_2_stage_2 => s!"        divide_2_stage_2"
| cp_stage_1 => s!"              cp_stage_1"
| update_visited_stage_2 => s!"  update_visited_stage_2"
| origin_0_stage_1 => s!"        origin_0_stage_1"
| origin_0_stage_7 => s!"        origin_0_stage_7"
| origin_1_stage_2 => s!"        origin_1_stage_2"
| divide_2_stage_1 => s!"        divide_2_stage_1"
| cp_twice_stage_5 => s!"        cp_twice_stage_5"
| origin_0_stage_6 => s!"        origin_0_stage_6"
| origin_0_stage_3 => s!"        origin_0_stage_3"
| init_pointer_stage_1 => s!"    init_pointer_stage_1"
| cp_twice_stage_2 => s!"        cp_twice_stage_2"
| update_visited_stage_1 => s!"  update_visited_stage_1"
| cp_twice_stage_3 => s!"        cp_twice_stage_3"
| cp_stage_5 => s!"              cp_stage_5"
| continue_collatz_stage_2 => s!"continue_collatz_stage_2"
| bootstrap_stage_1 => s!"       bootstrap_stage_1"
| init_pointer_stage_3 => s!"    init_pointer_stage_3"
| cp_twice_stage_1 => s!"        cp_twice_stage_1"
| init_pointer_stage_2 => s!"    init_pointer_stage_2"
| divide_2_stage_3 => s!"        divide_2_stage_3"
| origin_1_stage_4 => s!"        origin_1_stage_4"
| origin_1_stage_7 => s!"        origin_1_stage_7"
| origin_0_stage_5 => s!"        origin_0_stage_5"
| cp_stage_4 => s!"              cp_stage_4"
| odd => s!"                     odd"
| origin_0_stage_2 => s!"        origin_0_stage_2"
| even => s!"                    even"
| cp_twice_stage_4 => s!"        cp_twice_stage_4"
| cp_stage_3 => s!"              cp_stage_3"
| cp_twice_stage_6 => s!"        cp_twice_stage_6"
| origin_1_stage_1 => s!"        origin_1_stage_1"
| divide_2_stage_4 => s!"        divide_2_stage_4"
| unreachable => s!"                        unreachable"



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
def init (l : List Γ) : Cfg := ⟨bootstrap_stage_1, Turing.Tape.mk₁ l⟩

/-- Execution semantics of the Turing machine. -/
def step (M : Machine) : Cfg → Option Cfg :=
  fun ⟨q, T⟩ ↦ (M q T.1).map fun ⟨q', a⟩ ↦ ⟨q', (T.write a.write).move a.move⟩


def machine : Machine
| bootstrap_stage_1, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| bootstrap_stage_1, Γ.one => some ⟨unreachable, ⟨Turing.Dir.right, Γ.one⟩⟩
| bootstrap_stage_1, Γ.two => some ⟨cp_stage_5, ⟨Turing.Dir.right, Γ.one⟩⟩
| even, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| even, Γ.one => some ⟨odd, ⟨Turing.Dir.right, Γ.one⟩⟩
| even, Γ.two => some ⟨divide_2_stage_1, ⟨Turing.Dir.left, Γ.two⟩⟩
| odd, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| odd, Γ.one => some ⟨even, ⟨Turing.Dir.right, Γ.one⟩⟩
| odd, Γ.two => some ⟨cp_twice_stage_1, ⟨Turing.Dir.left, Γ.two⟩⟩
| divide_2_stage_1, Γ.zero => some ⟨init_pointer_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| divide_2_stage_1, Γ.one => some ⟨divide_2_stage_2, ⟨Turing.Dir.left, Γ.two⟩⟩
| divide_2_stage_1, Γ.two => some ⟨unreachable, ⟨Turing.Dir.left, Γ.two⟩⟩
| divide_2_stage_2, Γ.zero => some ⟨divide_2_stage_3, ⟨Turing.Dir.right, Γ.one⟩⟩
| divide_2_stage_2, Γ.one => some ⟨divide_2_stage_2, ⟨Turing.Dir.left, Γ.one⟩⟩
| divide_2_stage_2, Γ.two => some ⟨divide_2_stage_3, ⟨Turing.Dir.right, Γ.two⟩⟩
| divide_2_stage_3, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| divide_2_stage_3, Γ.one => some ⟨divide_2_stage_4, ⟨Turing.Dir.right, Γ.zero⟩⟩
| divide_2_stage_3, Γ.two => some ⟨unreachable, ⟨Turing.Dir.right, Γ.two⟩⟩
| divide_2_stage_4, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| divide_2_stage_4, Γ.one => some ⟨divide_2_stage_4, ⟨Turing.Dir.right, Γ.one⟩⟩
| divide_2_stage_4, Γ.two => some ⟨divide_2_stage_1, ⟨Turing.Dir.left, Γ.two⟩⟩
| cp_stage_1, Γ.zero => some ⟨cp_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_stage_1, Γ.one => some ⟨cp_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_stage_1, Γ.two => some ⟨cp_stage_2, ⟨Turing.Dir.right, Γ.two⟩⟩
| cp_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_stage_2, Γ.one => some ⟨cp_stage_3, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_stage_2, Γ.two => some ⟨even, ⟨Turing.Dir.right, Γ.two⟩⟩
| cp_stage_3, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_stage_3, Γ.one => some ⟨cp_stage_3, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_stage_3, Γ.two => some ⟨cp_stage_4, ⟨Turing.Dir.right, Γ.two⟩⟩
| cp_stage_4, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| cp_stage_4, Γ.one => some ⟨cp_stage_4, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_stage_4, Γ.two => some ⟨cp_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_stage_5, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| cp_stage_5, Γ.one => some ⟨cp_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_stage_5, Γ.two => some ⟨cp_stage_1, ⟨Turing.Dir.left, Γ.two⟩⟩
| cp_twice_stage_1, Γ.zero => some ⟨cp_twice_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_1, Γ.one => some ⟨cp_twice_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_twice_stage_1, Γ.two => some ⟨cp_twice_stage_2, ⟨Turing.Dir.right, Γ.two⟩⟩
| cp_twice_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_twice_stage_2, Γ.one => some ⟨cp_twice_stage_3, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_twice_stage_2, Γ.two => some ⟨update_visited_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_3, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| cp_twice_stage_3, Γ.one => some ⟨cp_twice_stage_3, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_3, Γ.two => some ⟨cp_twice_stage_4, ⟨Turing.Dir.right, Γ.two⟩⟩
| cp_twice_stage_4, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| cp_twice_stage_4, Γ.one => some ⟨cp_twice_stage_4, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_4, Γ.two => some ⟨cp_twice_stage_6, ⟨Turing.Dir.right, Γ.one⟩⟩
| cp_twice_stage_5, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| cp_twice_stage_5, Γ.one => some ⟨cp_twice_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_twice_stage_5, Γ.two => some ⟨cp_twice_stage_1, ⟨Turing.Dir.left, Γ.two⟩⟩
| cp_twice_stage_6, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| cp_twice_stage_6, Γ.one => some ⟨unreachable, ⟨Turing.Dir.left, Γ.one⟩⟩
| cp_twice_stage_6, Γ.two => some ⟨cp_twice_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| update_visited_stage_1, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| update_visited_stage_1, Γ.one => some ⟨update_visited_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| update_visited_stage_1, Γ.two => some ⟨update_visited_stage_2, ⟨Turing.Dir.left, Γ.two⟩⟩
| update_visited_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_visited_stage_2, Γ.one => some ⟨init_pointer_stage_1, ⟨Turing.Dir.left, Γ.zero⟩⟩
| update_visited_stage_2, Γ.two => some ⟨unreachable, ⟨Turing.Dir.left, Γ.two⟩⟩
| init_pointer_stage_1, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| init_pointer_stage_1, Γ.one => some ⟨init_pointer_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| init_pointer_stage_1, Γ.two => some ⟨init_pointer_stage_2, ⟨Turing.Dir.left, Γ.two⟩⟩
| init_pointer_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| init_pointer_stage_2, Γ.one => some ⟨init_pointer_stage_2, ⟨Turing.Dir.left, Γ.one⟩⟩
| init_pointer_stage_2, Γ.two => some ⟨init_pointer_stage_3, ⟨Turing.Dir.left, Γ.two⟩⟩
| init_pointer_stage_3, Γ.zero => some ⟨origin_0_stage_1, ⟨Turing.Dir.right, Γ.two⟩⟩
| init_pointer_stage_3, Γ.one => some ⟨origin_1_stage_1, ⟨Turing.Dir.right, Γ.two⟩⟩
| init_pointer_stage_3, Γ.two => some ⟨origin_0_stage_1, ⟨Turing.Dir.right, Γ.two⟩⟩
| origin_0_stage_1, Γ.zero => some ⟨origin_0_stage_1, ⟨Turing.Dir.right, Γ.zero⟩⟩
| origin_0_stage_1, Γ.one => some ⟨origin_0_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| origin_0_stage_1, Γ.two => some ⟨origin_0_stage_2, ⟨Turing.Dir.right, Γ.two⟩⟩
| origin_0_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| origin_0_stage_2, Γ.one => some ⟨origin_0_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| origin_0_stage_2, Γ.two => some ⟨origin_0_stage_3, ⟨Turing.Dir.right, Γ.two⟩⟩
| origin_0_stage_3, Γ.zero => some ⟨origin_0_stage_4, ⟨Turing.Dir.left, Γ.one⟩⟩
| origin_0_stage_3, Γ.one => some ⟨origin_0_stage_3, ⟨Turing.Dir.right, Γ.one⟩⟩
| origin_0_stage_3, Γ.two => some ⟨unreachable, ⟨Turing.Dir.left, Γ.two⟩⟩
| origin_0_stage_4, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_0_stage_4, Γ.one => some ⟨origin_0_stage_5, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_0_stage_4, Γ.two => some ⟨finish_0_stage_1, ⟨Turing.Dir.left, Γ.two⟩⟩
| origin_0_stage_5, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_0_stage_5, Γ.one => some ⟨origin_0_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| origin_0_stage_5, Γ.two => some ⟨origin_0_stage_6, ⟨Turing.Dir.left, Γ.two⟩⟩
| origin_0_stage_6, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_0_stage_6, Γ.one => some ⟨origin_0_stage_6, ⟨Turing.Dir.left, Γ.one⟩⟩
| origin_0_stage_6, Γ.two => some ⟨origin_0_stage_7, ⟨Turing.Dir.left, Γ.two⟩⟩
| origin_0_stage_7, Γ.zero => some ⟨origin_0_stage_7, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_0_stage_7, Γ.one => some ⟨origin_0_stage_7, ⟨Turing.Dir.left, Γ.one⟩⟩
| origin_0_stage_7, Γ.two => some ⟨init_pointer_stage_3, ⟨Turing.Dir.left, Γ.zero⟩⟩
| finish_0_stage_1, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| finish_0_stage_1, Γ.one => some ⟨finish_0_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| finish_0_stage_1, Γ.two => some ⟨finish_0_stage_2, ⟨Turing.Dir.left, Γ.two⟩⟩
| finish_0_stage_2, Γ.zero => some ⟨finish_0_stage_2, ⟨Turing.Dir.left, Γ.zero⟩⟩
| finish_0_stage_2, Γ.one => some ⟨finish_0_stage_2, ⟨Turing.Dir.left, Γ.one⟩⟩
| finish_0_stage_2, Γ.two => some ⟨check_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| origin_1_stage_1, Γ.zero => some ⟨origin_1_stage_1, ⟨Turing.Dir.right, Γ.zero⟩⟩
| origin_1_stage_1, Γ.one => some ⟨origin_1_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| origin_1_stage_1, Γ.two => some ⟨origin_1_stage_2, ⟨Turing.Dir.right, Γ.two⟩⟩
| origin_1_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| origin_1_stage_2, Γ.one => some ⟨origin_1_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| origin_1_stage_2, Γ.two => some ⟨origin_1_stage_3, ⟨Turing.Dir.right, Γ.two⟩⟩
| origin_1_stage_3, Γ.zero => some ⟨origin_1_stage_4, ⟨Turing.Dir.left, Γ.one⟩⟩
| origin_1_stage_3, Γ.one => some ⟨origin_1_stage_3, ⟨Turing.Dir.right, Γ.one⟩⟩
| origin_1_stage_3, Γ.two => some ⟨unreachable, ⟨Turing.Dir.left, Γ.two⟩⟩
| origin_1_stage_4, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_1_stage_4, Γ.one => some ⟨origin_1_stage_5, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_1_stage_4, Γ.two => none
| origin_1_stage_5, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_1_stage_5, Γ.one => some ⟨origin_1_stage_5, ⟨Turing.Dir.left, Γ.one⟩⟩
| origin_1_stage_5, Γ.two => some ⟨origin_1_stage_6, ⟨Turing.Dir.left, Γ.two⟩⟩
| origin_1_stage_6, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_1_stage_6, Γ.one => some ⟨origin_1_stage_6, ⟨Turing.Dir.left, Γ.one⟩⟩
| origin_1_stage_6, Γ.two => some ⟨origin_1_stage_7, ⟨Turing.Dir.left, Γ.two⟩⟩
| origin_1_stage_7, Γ.zero => some ⟨origin_1_stage_7, ⟨Turing.Dir.left, Γ.zero⟩⟩
| origin_1_stage_7, Γ.one => some ⟨origin_1_stage_7, ⟨Turing.Dir.left, Γ.one⟩⟩
| origin_1_stage_7, Γ.two => some ⟨init_pointer_stage_3, ⟨Turing.Dir.left, Γ.one⟩⟩
| check_1, Γ.zero => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.zero⟩⟩
| check_1, Γ.one => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| check_1, Γ.two => some ⟨cleanup_visited, ⟨Turing.Dir.left, Γ.two⟩⟩
| continue_collatz_stage_1, Γ.zero => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.zero⟩⟩
| continue_collatz_stage_1, Γ.one => some ⟨continue_collatz_stage_1, ⟨Turing.Dir.right, Γ.one⟩⟩
| continue_collatz_stage_1, Γ.two => some ⟨continue_collatz_stage_2, ⟨Turing.Dir.right, Γ.two⟩⟩
| continue_collatz_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| continue_collatz_stage_2, Γ.one => some ⟨continue_collatz_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| continue_collatz_stage_2, Γ.two => some ⟨even, ⟨Turing.Dir.right, Γ.two⟩⟩
| cleanup_visited, Γ.zero => some ⟨cleanup_visited, ⟨Turing.Dir.left, Γ.two⟩⟩
| cleanup_visited, Γ.one => some ⟨cleanup_visited, ⟨Turing.Dir.left, Γ.two⟩⟩
| cleanup_visited, Γ.two => some ⟨plus_1_stage_1, ⟨Turing.Dir.right, Γ.two⟩⟩
| plus_1_stage_1, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| plus_1_stage_1, Γ.one => some ⟨plus_1_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| plus_1_stage_1, Γ.two => some ⟨plus_1_stage_1, ⟨Turing.Dir.right, Γ.two⟩⟩
| plus_1_stage_2, Γ.zero => some ⟨unreachable, ⟨Turing.Dir.right, Γ.zero⟩⟩
| plus_1_stage_2, Γ.one => some ⟨plus_1_stage_2, ⟨Turing.Dir.right, Γ.one⟩⟩
| plus_1_stage_2, Γ.two => some ⟨cp_stage_1, ⟨Turing.Dir.left, Γ.one⟩⟩
| unreachable, _ => none -- TODO


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

end Tm45_3
