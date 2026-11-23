import Mathlib
import Formalism.BehrendSets.StatementE
import Formalism.BehrendSets.BehrendVariance.ProbEqSumIte
import Formalism.BehrendSets.BehrendVariance.Select

open Finset

noncomputable section

namespace Formalism.BehrendSets.E4

open Formalism.BehrendSets Formalism.BehrendSets.Rand

variable {α : Type} [DecidableEq α]

lemma residue (o j i : ℕ) (hj : j < o) (hd : o ∣ j + i) : (o - i % o) % o = j := by
  have ho : 0 < o := by omega
  have hr : i % o < o := Nat.mod_lt _ ho
  have h0 : (j + i % o) % o = 0 := by
    rw [Nat.add_mod_mod]
    exact Nat.mod_eq_zero_of_dvd hd
  by_cases hlt : j + i % o < o
  · rw [Nat.mod_eq_of_lt hlt] at h0
    have hi0 : i % o = 0 := by omega
    rw [hi0, Nat.sub_zero, Nat.mod_self]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h0
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end Formalism.BehrendSets.E4

namespace Formalism.BehrendSets

open Formalism.BehrendSets.Rand Formalism.BehrendSets.E4

end Formalism.BehrendSets
