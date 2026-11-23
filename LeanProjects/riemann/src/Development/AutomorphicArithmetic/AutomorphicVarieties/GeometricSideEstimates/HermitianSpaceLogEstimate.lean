import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideUpperBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GlobalGeometricEstimateOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.RationalPointRetractionExistsCmDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.PointEvaluationMultiplicativeTsum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGeometricEstimate
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic

private theorem log_bound {T D C H q : ℝ} {N M : ℕ} (hT : 1 ≤ T) (hC : 1 ≤ C) (hH : 1 ≤ H) (hq : 1 ≤ q)
    (hHq : H ≤ 2 * q) (h : T ≤ D / ((C * H ^ N)⁻¹) ^ M) :
    Real.log T ≤ (|Real.log D| + M * Real.log C + M * N) * (1 + Real.log q) := by
  have hC0 : 0 < C := one_pos.trans_le hC
  have hH0 : 0 < H := one_pos.trans_le hH
  have hq0 : 0 < q := one_pos.trans_le hq
  rw [inv_pow, div_inv_eq_mul] at h
  have hp : 0 < (C * H ^ N) ^ M := by positivity
  have hD : 0 < D := (mul_pos_iff_of_pos_right hp).1 (one_pos.trans_le (hT.trans h))
  have h1 : Real.log T ≤ Real.log D + M * (Real.log C + N * Real.log H) := by
    have := Real.log_le_log (one_pos.trans_le hT) h
    rwa [Real.log_mul hD.ne' hp.ne', Real.log_pow, Real.log_mul hC0.ne' (by positivity), Real.log_pow] at this
  have h2 : Real.log H ≤ 1 + Real.log q := by
    have := Real.log_le_log hH0 hHq
    rw [Real.log_mul two_ne_zero hq0.ne'] at this
    have h3 := Real.log_le_sub_one_of_pos (two_pos (α := ℝ))
    linarith
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  have h4 : (M : ℝ) * N * Real.log H ≤ M * N * (1 + Real.log q) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : 0 ≤ (|Real.log D| + M * Real.log C) * Real.log q := by positivity
  have h6 := le_abs_self (Real.log D)
  nlinarith

theorem UpperTheory.hermitian_space_log_estimate :
    FnLe := by
  intro E _ _ _ a ha L hL
  obtain ⟨C, N, hC, hmin⟩ := UpperTheory.global_geometric_estimate_of_local E a ha L hL
  obtain ⟨M, hsc⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨D, -, hup⟩ := UpperTheory.geometric_side_upper_bound M
  obtain ⟨-, hrt, hγ, -⟩ := UpperTheory.rationalPoint_retraction_exists_cmDatum E a ha
  obtain ⟨hTh, -⟩ := UpperTheory.hermitian_space_geometric_estimate E a ha L hL
  refine ⟨|Real.log D| + M * Real.log C + M * N, fun g => ?_⟩
  have hq : 1 ≤ qht g := (UpperTheory.V.Lit.Geo.qhtFacts E a).1 g
  obtain ⟨γ, hlt⟩ := exists_lt_of_ciInf_lt (show qht g < 2 * qht g by linarith)
  change AutomorphicForm.height (K := E) (ratGL E a γ * rt g) < _ at hlt
  have hH := AutomorphicForm.one_le_height (K := E) (ratGL E a γ * rt g)
  have hCH : 1 ≤ C * AutomorphicForm.height (K := E) (ratGL E a γ * rt g) ^ N :=
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hH)
  refine log_bound (hTh g).1 hC hH hq hlt.le ?_
  refine hup _ _ (0 : lat L g) _ (hsc g) (inv_pos.2 (one_pos.trans_le hCH)) (inv_le_one_of_one_le₀ hCH) fun v hv => ?_
  have e : (v.1 ᵥ* (γ⁻¹).val) ᵥ* γ.val = v.1 := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have hw := hγ γ (rt g) (v.1 ᵥ* (γ⁻¹).val)
  rw [e, (hrt g).2.2] at hw
  have h1 := hmin (ratGL E a γ * rt g) (v.1 ᵥ* (γ⁻¹).val)
    (by
      change ptF _ _ ∈ L
      rw [hw.1]
      exact v.2)
    (fun h0 => hv (Subtype.ext (by
      rw [← e, h0, Matrix.zero_vecMul]
      rfl)))
  rw [hw.2] at h1
  rw [inv_le_iff_one_le_mul₀' (one_pos.trans_le hCH)]
  exact h1
