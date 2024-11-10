import Mathlib.Computability.TuringMachine
import Mathlib.Data.Nat.Prime.Defs

namespace Tm45_3

inductive Γ
  | zero
  | one
  | two
   deriving DecidableEq

instance : Inhabited Γ := ⟨ Γ.two ⟩

instance : ToString Γ where
  toString
    | Γ.zero => "0"
    | Γ.one => "1"
    | Γ.two => "#"

structure Stmt where
  move : Turing.Dir
  write : Γ

end Tm45_3
