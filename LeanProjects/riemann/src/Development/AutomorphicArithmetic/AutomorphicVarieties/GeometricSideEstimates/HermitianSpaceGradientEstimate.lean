import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TraceFormCauchySchwarzCmDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
open UpperTheory.V.Lit.Geo

private theorem gradB_pt {z n W q c : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (h1 : n ^ 2 ≤ z) (h2 : z ≤ W * q) (h3 : z = 0 ∨ c ≤ n) :
    z ≤ W ^ 2 / c ^ 2 * (1 + q) ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  rcases h3 with h | h
  · rw [h]; positivity
  · have hz : c ^ 2 ≤ z := (pow_le_pow_left₀ hc.le h 2).trans h1
    have hz0 : 0 ≤ z := hc2.le.trans hz
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    have a1 : z * c ^ 2 ≤ z * z := mul_le_mul_of_nonneg_left hz hz0
    have a2 : z * z ≤ (W * q) * (W * q) := mul_self_le_mul_self hz0 h2
    have a3 : q ^ 2 ≤ (1 + q) ^ 2 := by nlinarith
    have a4 : W ^ 2 * q ^ 2 ≤ W ^ 2 * (1 + q) ^ 2 := mul_le_mul_of_nonneg_left a3 (sq_nonneg W)
    nlinarith

theorem UpperTheory.hermitian_space_gradient_estimate :
    GradB := by
  intro E _ _ _ a ha L hL
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C, hC0, hC⟩ := UpperTheory.moment_bound_of_pointwise_moments N 2
  refine ⟨C, fun g w c hc hsep => ?_⟩
  obtain ⟨hs, hle⟩ := hC _ _ (hN g)
  have hTh : 1 ≤ Th L g := ((UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1 g).1
  have hTh0 : 0 < Th L g := lt_of_lt_of_le one_pos hTh
  have hR := (UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w).2.2
  rw [UpperTheory.hermitian_space_moment_identity E a ha L hL g, div_le_iff₀ hTh0]
  have hK : 0 ≤ qf w ^ 2 / c ^ 2 := by positivity
  have hpt : ∀ v : lat L g, quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) ≤
      qf w ^ 2 / c ^ 2 * ((1 + qf (pt (rt g) v.1)) ^ 2 * Real.exp (-Real.pi * qf (pt (rt g) v.1))) := by
    intro v
    obtain ⟨r1, r2, r3⟩ := hR (pt (rt g) v.1)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (gradB_pt hc (qf_nonneg _) r1 r2 ((hsep v.1 v.2).imp r3 id)) (Real.exp_pos _).le
  have hnn : ∀ v : lat L g, 0 ≤ quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) :=
    fun v => mul_nonneg ((sq_nonneg _).trans (hR _).1) (Real.exp_pos _).le
  have hs2 := hs.mul_left (qf w ^ 2 / c ^ 2)
  have hs1 := Summable.of_nonneg_of_le hnn hpt hs2
  refine (hs1.tsum_le_tsum hpt hs2).trans ?_
  rw [tsum_mul_left]
  refine (mul_le_mul_of_nonneg_left hle hK).trans (le_of_eq ?_)
  change _ * (C * Th L g) = _
  ring
