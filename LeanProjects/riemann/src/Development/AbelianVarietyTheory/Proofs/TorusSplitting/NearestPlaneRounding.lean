import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.AbsTwoMulInnerLeOfNormSubEqInfDist

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

theorem nearestPlane_rounding : Ext.NearestPlane := by
  intro V _ _ n v _ x hx
  obtain ⟨w, hw, hle⟩ := exists_int_comb_norm_sub_sq_le n v hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hw
  refine ⟨c, ?_⟩
  have hsum : ∑ i, ((c i : ℤ) : ℝ) • v i = ∑ i, c i • v i := by
    simp only [Int.cast_smul_eq_zsmul]
  rw [hsum]
  linarith

end GlobalTheory
