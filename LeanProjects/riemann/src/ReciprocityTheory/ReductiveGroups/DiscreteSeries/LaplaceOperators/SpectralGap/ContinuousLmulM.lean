import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.ContinuousBlkWConj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Groups

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem continuous_lmulM' {k r : ℕ} (s : Mat k r) : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) s) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Formalism.QuantumDeterminants.lmulM, Matrix.mul_apply, Matrix.of_apply]
  exact continuous_finsetSum _ fun l _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply l))

def ptsOf {k r : ℕ} (U : Set (Mat k r)) : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ U}

def ptsGroup {k r : ℕ} {U : Set (Mat k r)} (hU : Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) : Group (ptsOf U) where
  mul a b := ⟨(Matrix.of a.1 * Matrix.of b.1 : Mat k r), hU.mul_mem (Matrix.of a.1) a.2 (Matrix.of b.1) b.2⟩
  one := ⟨(1 : Mat k r), hU.one_mem⟩
  inv a := ⟨((Matrix.of a.1)⁻¹ : Mat k r), hU.inv_mem (Matrix.of a.1) a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1) (hU.unit (Matrix.of a.1) a.2))

end ReciprocityTheory.ChartRestriction.DS.Lap
