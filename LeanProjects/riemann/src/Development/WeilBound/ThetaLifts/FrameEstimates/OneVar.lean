import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKEst

open scoped NNReal ENNReal
open MeasureTheory Metric

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_sep (Λ : Submodule ℤ V) [DiscreteTopology Λ] :
    ∃ ε : ℝ, 0 < ε ∧ Pairwise (Function.onFun Disjoint fun x : Λ => ball (x : V) ε) := by
  obtain ⟨δ, hδ, h⟩ := Metric.isOpen_iff.1 (isOpen_discrete ({0} : Set Λ)) 0 rfl
  refine ⟨δ / 2, by positivity, fun x y hxy => ?_⟩
  apply Metric.ball_disjoint_ball
  by_contra hlt
  push Not at hlt
  apply hxy
  have hm : x - y ∈ ball (0 : Λ) δ := by
    rw [mem_ball_zero_iff]
    have : ‖x - y‖ = dist (x : V) (y : V) := by
      rw [dist_eq_norm]; rfl
    linarith
  exact sub_eq_zero.1 (h hm)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem oneVar_pt {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) (N : ℕ) {x y : V} (hy : y ∈ ball x ε) :
    ((1 + c * ‖x‖) ^ N)⁻¹ ≤ (1 + ε) ^ N * ((1 + ‖c • (1 : ℝ)‖ * ‖y‖) ^ N)⁻¹ := by
  have hcn : ‖c • (1 : ℝ)‖ = c := by simp [abs_of_pos hc]
  rw [hcn]
  have h1 : ‖y‖ ≤ ‖x‖ + ε := by
    have := mem_ball_iff_norm.1 hy
    have h2 := norm_le_norm_add_norm_sub' y x
    linarith
  have hx := norm_nonneg x
  have hy0 := norm_nonneg y
  have h2 : 1 + c * ‖y‖ ≤ (1 + ε) * (1 + c * ‖x‖) := by
    have : c * ‖y‖ ≤ c * (‖x‖ + ε) := mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : c * ε ≤ ε := by nlinarith
    have h4 : 0 ≤ ε * (c * ‖x‖) := by positivity
    nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 N

theorem oneVar_core (Λ : Submodule ℤ V) [DiscreteTopology Λ] (N : ℕ) (hN : Module.finrank ℝ V < N) :
    ∃ K : ℝ≥0, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ K * ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) := by
  borelize V
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  set μ : Measure V := Measure.addHaar with hμ
  obtain ⟨ε, hε, hd⟩ := oneVar_sep Λ
  set f : V → ℝ≥0∞ := fun y => ENNReal.ofReal (((1 + ‖y‖) ^ N)⁻¹) with hf
  have hfm : Measurable f := by
    rw [hf]; fun_prop
  have hI : ∫⁻ y, f y ∂μ < ⊤ := by
    have := finite_integral_one_add_norm (E := V) (μ := μ) (r := (N : ℝ)) (by exact_mod_cast hN)
    refine lt_of_eq_of_lt (lintegral_congr fun y => ?_) this
    rw [hf, Real.rpow_neg (by positivity), Real.rpow_natCast]
  set b : ℝ≥0∞ := μ (ball (0 : V) ε) with hb
  have hb0 : b ≠ 0 := (measure_ball_pos μ _ hε).ne'
  have hbt : b ≠ ⊤ := measure_ball_lt_top.ne
  set A : ℝ≥0∞ := ENNReal.ofReal ((1 + ε) ^ N) with hA
  have hK : b⁻¹ * A * ∫⁻ y, f y ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hb0) ENNReal.ofReal_ne_top) hI.ne
  refine ⟨(b⁻¹ * A * ∫⁻ y, f y ∂μ).toNNReal, fun c hc hc1 => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  have hsc : ∫⁻ y, f (c • y) ∂μ = ENNReal.ofReal ((c ^ Module.finrank ℝ V)⁻¹) * ∫⁻ y, f y ∂μ := by
    rw [← lintegral_map hfm (measurable_const_smul c), Measure.map_addHaar_smul μ hc.ne', lintegral_smul_measure,
      abs_of_pos (by positivity), smul_eq_mul]
  have hpt : ∀ x : Λ, b * ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y in ball (x : V) ε, f (c • y) ∂μ := by
    intro x
    have e1 : b = μ (ball (x : V) ε) := (Measure.addHaar_ball_center μ _ _).symm
    rw [e1, mul_comm, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
    simp only [hf]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := oneVar_pt hc hc1 hε N hy
    simpa [norm_smul] using this
  have hsum : b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹) ≤ A * ∫⁻ y, f (c • y) ∂μ := by
    rw [← ENNReal.tsum_mul_left]
    refine (ENNReal.tsum_le_tsum hpt).trans ?_
    rw [ENNReal.tsum_mul_left, ← lintegral_iUnion (fun _ => measurableSet_ball) hd]
    gcongr
    exact Measure.restrict_le_self
  calc ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)
      = b⁻¹ * (b * ∑' x : Λ, ENNReal.ofReal (((1 + c * ‖(x : V)‖) ^ N)⁻¹)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, one_mul]
    _ ≤ b⁻¹ * (A * ∫⁻ y, f (c • y) ∂μ) := by gcongr
    _ = _ := by rw [hsc]; ring

end

theorem oneVar_of : OneVar := by
  intro V _ _ _ Λ _ N hN
  obtain ⟨K, hK⟩ := oneVar_core Λ N hN
  refine ⟨K, fun l => ?_⟩
  have h := hK (Real.exp (-max 0 l)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by simp))
  rw [← Real.exp_nat_mul, ← Real.exp_neg, mul_neg, neg_neg] at h
  refine le_trans (ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_) h
  have : Real.exp (-max 0 l) ≤ Real.exp (-l) := Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
  gcongr

end PositivityTheory.ThKEst

end
