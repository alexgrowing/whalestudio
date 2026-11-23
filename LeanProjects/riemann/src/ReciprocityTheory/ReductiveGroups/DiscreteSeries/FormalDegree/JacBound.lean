import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem jac_le_exp {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    Jac z ≤ Real.exp (((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (hs (pmat z))) := by
  have hpos : 0 < Jac z := lt_of_lt_of_le one_pos (jac_ge_one z)
  have h := log_jac_le_rho z
  rw [rhoP, ← mul_assoc] at h
  calc Jac z = Real.exp (Real.log (Jac z)) := (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr h

end ReciprocityTheory.ChartRestriction.DS
