import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.CompanionTheory.FSCrofton.HessFrame

private lemma contDiffOn_norm_sq_of_differentiableOn {d : ℕ} {U : Set (V d)} (hU : IsOpen U) {f : V d → ℂ}
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℝ ∞ (fun v => ‖f v‖ ^ 2) U :=
  (contDiff_norm_sq ℝ).comp_contDiffOn
    ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn d f U hU hf).restrict_scalars ℝ)

theorem cHess_log_sum_normSq_eq (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α)
    (U : Set (V d)) (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (h0 : ∀ z ∈ U, b j₀ z ≠ 0) : ∀ z ∈ U,
    cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z =
      cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ))
        z := by
  intro z hz
  obtain ⟨R, hRdef⟩ : ∃ R : V d → ℝ,
      R = fun v => 1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2 := ⟨_, rfl⟩
  have hpos : ∀ v ∈ U, 0 < ‖b j₀ v‖ ^ 2 := fun v hv => pow_pos (norm_pos_iff.2 (h0 v hv)) 2
  have hRpos : ∀ v, 0 < R v := fun v => by rw [hRdef]; positivity
  have hp : ContDiffOn ℝ ∞ (fun v => Real.log (‖b j₀ v‖ ^ 2)) U :=
    (contDiffOn_norm_sq_of_differentiableOn hU (hb j₀)).log fun v hv => (hpos v hv).ne'
  have hq : ContDiffOn ℝ ∞ (fun v => Real.log (R v)) U := by
    refine ContDiffOn.log ?_ fun v _ => (hRpos v).ne'
    rw [hRdef]
    exact contDiffOn_const.add
      (ContDiffOn.sum fun j _ => contDiffOn_norm_sq_of_differentiableOn hU (by
        simpa only [div_eq_mul_inv] using (hb j.1).fun_mul ((hb j₀).fun_inv h0)))
  have hsplit : ∀ v ∈ U, ∑ j, ‖b j v‖ ^ 2 = ‖b j₀ v‖ ^ 2 * R v := by
    intro v hv
    have hn : ‖b j₀ v‖ ^ 2 ≠ 0 := (hpos v hv).ne'
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
      Finset.sum_subtype (F := inferInstance) (Finset.univ.erase j₀) (p := fun j => j ≠ j₀) (by simp),
      hRdef]
    simp only [mul_add, mul_one, Finset.mul_sum, norm_div, div_pow, mul_div_cancel₀ _ hn]
  have hev : (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun v => ((Real.log (‖b j₀ v‖ ^ 2) + 1 * Real.log (R v) : ℝ) : ℂ) := by
    refine Filter.eventually_of_mem (hU.mem_nhds hz) fun v hv => ?_
    simp only
    rw [hsplit v hv, Real.log_mul (hpos v hv).ne' (hRpos v).ne', one_mul]
  have hzero : cHess d (fun w => ((Real.log (‖b j₀ w‖ ^ 2) : ℝ) : ℂ)) z = 0 := by
    ext j k
    simp only [cHess, Matrix.of_apply, Matrix.zero_apply]
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log hU hz (hb j₀) h0 j k
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr hev,
    ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hU hp hq 1 hz, hzero, zero_add, Complex.ofReal_one,
    one_smul, hRdef]

end GlobalTheory.CompanionTheory.FSCrofton.HessFrame
