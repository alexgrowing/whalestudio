import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

open GlobalTheory.CovTest GlobalTheory.FlagPoly

namespace GlobalTheory.FlagBlockDim

theorem choose_two_add (j m : ℕ) : (j + m) * (j + m - 1) / 2 = j * m + j * (j - 1) / 2 + m * (m - 1) / 2 := by
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, Nat.choose_succ_succ', ih, Nat.choose_succ_succ', Nat.choose_one_right, Nat.choose_one_right]
    ring

theorem dimGr_add_sum (ι : Type) [Fintype ι] (N j : ℕ) (hj : j ≤ N) :
    dimGr ι N j + ∑ a : ι × Bool, rkB ι N j a * (rkB ι N j a - 1) / 2 = Formalism.DegreeFormula.dimFl ι N := by
  have hs : ∑ a : ι × Bool, rkB ι N j a * (rkB ι N j a - 1) / 2 =
      Fintype.card ι * (j * (j - 1) / 2 + (N - j) * (N - j - 1) / 2) := by
    rw [Fintype.sum_prod_type]
    simp [rkB, Finset.sum_const, Finset.card_univ, add_comm]
  rw [hs, dimGr, Formalism.DegreeFormula.dimFl, ← mul_add]
  congr 1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [choose_two_add, Nat.add_sub_cancel_left]
  ring

theorem dim_eq_dimGr_add {D : Formalism.BasicNotions.D7} (O : GlobalTheory.Mean4O.Setup D) (c : O.s.Comp) :
    dimGr D.what₂.Tau O.N O.j +
        ∑ a : D.what₂.Tau × Bool, rkB D.what₂.Tau O.N O.j a * (rkB D.what₂.Tau O.N O.j a - 1) / 2 =
      (O.var c).dim := by
  rw [dimGr_add_sum _ _ _ O.indef.2.le]
  exact (O.dim_eq c).symm

end GlobalTheory.FlagBlockDim
