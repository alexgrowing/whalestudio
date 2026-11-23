import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory
open Complex ComplexConjugate

theorem wdb_normSq_div {n : ℕ} (ρ : ℝ) (j : Fin n) (z : V n) :
    wdb n j (fun w : V n => (((‖w‖ ^ 2 / ρ ^ 2 : ℝ)) : ℂ)) z = z j / (ρ ^ 2 : ℝ) := by
  have h1 := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).const_smul ((ρ ^ 2)⁻¹ : ℝ)
  have e : (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) = fun w => ((ρ ^ 2)⁻¹ : ℝ) • ‖w‖ ^ 2 := by
    funext w; simp [smul_eq_mul, div_eq_inv_mul]
  have hv : HasFDerivAt (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) (((ρ ^ 2)⁻¹ : ℝ) • (2 • innerSL ℝ z)) z := by
    rw [e]; exact h1
  unfold wdb
  rw [fderiv_ofReal_apply hv.differentiableAt, fderiv_ofReal_apply hv.differentiableAt, hv.fderiv]
  simp only [bas, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  have hr : ∀ x y : V n, inner ℝ x y = re (inner ℂ x y) := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [hr, hr, inner_smul_right,
    EuclideanSpace.inner_single_right]
  rw [div_eq_mul_inv (z j), ← Complex.ofReal_inv]
  generalize (ρ ^ 2)⁻¹ = r
  apply Complex.ext <;> simp <;> ring

theorem wdb_cutoff_sq_le : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ (z : V n) (ξ : Fin n → ℂ), ‖∑ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ if ρ / 2 ≤ ‖z‖ ∧ ‖z‖ < ρ then A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 else 0 := by
  intro χ A hχ h01 h1 h0 hA n ρ hρ z ξ
  have hdχ : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hv : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) z :=
    by
    have := (differentiableAt_id (x := z)).norm_sq ℝ
    simpa [div_eq_mul_inv] using this.mul_const ((ρ ^ 2)⁻¹)
  set t := ‖z‖ ^ 2 / ρ ^ 2 with ht
  have hw : ∀ j, wdb n j (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) : ℝ) : ℂ)) z =
      ((deriv χ t : ℝ) : ℂ) * (z j / ((ρ ^ 2 : ℝ) : ℂ)) := by
    intro j
    rw [wdb_ofReal_comp (k := χ) (v := fun w : V n => ‖w‖ ^ 2 / ρ ^ 2) (hdχ _) hv,
      wdb_normSq_div]
  simp_rw [hw]
  have hsum : ∑ j, ((deriv χ t : ℝ) : ℂ) * (z j / ((ρ ^ 2 : ℝ) : ℂ)) * (starRingEnd ℂ) (ξ j) =
      ((deriv χ t : ℝ) : ℂ) / ((ρ ^ 2 : ℝ) : ℂ) * ∑ j, z j * (starRingEnd ℂ) (ξ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  split_ifs with hann
  · have hCS : ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ ‖z‖ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by
      calc ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖z j‖ * ‖ξ j‖) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _)
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, Complex.norm_conj]
        _ ≤ (∑ j, ‖z j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = ‖z‖ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by rw [EuclideanSpace.norm_sq_eq]
    have hz : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hann.2.le 2
    have hS : ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 :=
      hCS.trans (mul_le_mul_of_nonneg_right hz (Finset.sum_nonneg fun j _ => by positivity))
    have hd : |deriv χ t| ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hA t) 2
    have hρ2 : (0 : ℝ) < ρ ^ 2 := by positivity
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hρ2, mul_pow, div_pow]
    calc |deriv χ t| ^ 2 / (ρ ^ 2) ^ 2 * ‖∑ j, z j * (starRingEnd ℂ) (ξ j)‖ ^ 2
        ≤ A ^ 2 / (ρ ^ 2) ^ 2 * (ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) := by gcongr
      _ = A ^ 2 / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2 := by field_simp
  · have hd0 : deriv χ t = 0 := by
      rcases not_and_or.mp hann with h | h
      · push_neg at h
        have ht4 : t ≤ 1 / 4 := by
          rw [ht, div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg z]
        apply IsLocalMax.deriv_eq_zero
        exact Filter.Eventually.of_forall fun s => by rw [h1 t ht4]; exact (h01 s).2
      · push_neg at h
        have ht1 : 1 ≤ t := by
          rw [ht, le_div_iff₀ (by positivity)]; nlinarith
        apply IsLocalMin.deriv_eq_zero
        exact Filter.Eventually.of_forall fun s => by rw [h0 t ht1]; exact (h01 s).1
    rw [hd0]; simp

end GlobalTheory
