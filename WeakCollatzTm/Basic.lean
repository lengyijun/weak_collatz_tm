import Mathlib.Data.Nat.Prime.Defs

theorem unlimitedQ (Q : ℕ → Prop)
               (base : ℕ) (hbase : Q base)
               (hq : ∀ x, Q x → ∃ y > x, Q y) :
               ∀ n, ∃ m > n, Q m := by
intros n
induction n with
| zero => cases base with
          | zero => apply hq at hbase
                    tauto
          | succ base => use (base+1)
                         constructor
                         . omega
                         . tauto
| succ n induction_step =>
            obtain ⟨m, _, _⟩ := induction_step
            by_cases hm: m = n + 1
            . subst m
              apply hq
              tauto
            . use m
              constructor
              . omega
              . assumption


/-
P i => nth_cfg i ≠ none
Q i n => nth_cfg i = some ⟨⟨25, by omega⟩, ⟨Γ.zero, Turing.ListBlank.mk (List.replicate (2*n+4) Γ.one), Turing.ListBlank.mk []⟩⟩
-/
theorem propagating_induction (P : ℕ → Prop) (Q : ℕ → ℕ → Prop)
               (base : ℕ) (hbase : Q base 0)
               (hq : ∀ i n, Q i n → ∃ j > i, Q j (n+1))
               (pq : ∀ i n, Q i n → ∀ j ≤ i, P j)
: ∀ j, P j := by
intro j
have h := unlimitedQ (fun i => ∃ n, Q i n) base ⟨0, hbase⟩
simp at h
refine (?_ ∘ h) ?_
. intros g
  obtain ⟨i, hi, n, hqin⟩ := g j
  apply pq i n hqin
  omega
. intros i m hqim
  obtain ⟨j, _, _⟩ := hq i m hqim
  use j
  constructor
  . omega
  . use (m+1)
