import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartCover
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnifBergmanLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights

noncomputable section

lemma gaussDiscMass_pos {lam R : ℝ} (hlam : 0 ≤ lam) (hR : 0 < R) : 0 < gaussDiscMass lam R := by
  unfold gaussDiscMass
  split_ifs with h
  · positivity
  · have hl : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h)
    have : Real.exp (-lam * R ^ 2) < 1 :=
      (Real.exp_lt_exp.2 (by nlinarith [sq_pos_of_pos hR] : -lam * R ^ 2 < 0)).trans_eq Real.exp_zero
    have : 0 < 1 - Real.exp (-lam * R ^ 2) := by linarith
    positivity

theorem UniformBergmanBound.proof (hP : PolydiscSubmean.Statement)
    (hC : ChartTaylorCover.Statement) : UniformBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV _ _
  obtain ⟨r, hr, M, c, hc, hcov⟩ := hC A L W₀ W₁ dV
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hI : 0 < gaussDiscMass M' r := gaussDiscMass_pos hM'0 hr
  have hK : 0 < c * gaussDiscMass M' r ^ D := by positivity
  refine ⟨(c * gaussDiscMass M' r ^ D)⁻¹, fun n hn t ht V _ hV x => ?_⟩
  have hn0 : 0 < n := hn
  have hnD : 0 < (n : ℝ) ^ D := by positivity
  obtain ⟨j, hxj, hball, hdens, hW⟩ := hcov x
  obtain ⟨ℓ₀, h₀⟩ := hW W₀ (by simp)
  obtain ⟨ℓ₁, h₁⟩ := hW W₁ (by simp)
  set e := A.chart j
  set y := e x
  set ψ : (Fin D → ℂ) → ℝ := (W₀.lerp W₁ t).φ j ∘ e.symm with hψ
  have hψy : ψ y = (W₀.lerp W₁ t).φ j x := by simp [hψ, y, e.left_inv hxj]
  have hsub : Metric.closedBall y r ⊆ e.target ∩ e.symm ⁻¹' e.source :=
    fun w hw => ⟨hball hw, e.map_target (hball hw)⟩

  have hT : ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
      ψ (y + z) ≤ ψ y + (ℓ₀ + t • (ℓ₁ - ℓ₀)) z + M' * ∑ i, ‖z i‖ ^ 2 := by
    intro z hz
    have a₀ := h₀ z hz
    have a₁ := h₁ z hz
    have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
    have hMM : M * ∑ i, ‖z i‖ ^ 2 ≤ M' * ∑ i, ‖z i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    rw [hψy]
    simp only [hψ, Function.comp, Weight.lerp, FunLike.coe_add,
      FunLike.coe_smul, FunLike.coe_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    nlinarith [mul_le_mul_of_nonneg_left a₀ ht1, mul_le_mul_of_nonneg_left a₁ ht0]

  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV s.2
  have hs' : _ ∧ _ ∧ _ := hs
  set F : (Fin D → ℂ) → ℂ := (s : Fin A.n → X → ℂ) j ∘ e.symm with hF
  have hFa : AnalyticOnNhd ℂ F (Metric.closedBall y r) := ((hs'.1 j) j).mono hsub
  have hψc : ContinuousOn ψ (Metric.closedBall y r) :=
    (((W₀.lerp W₁ t).smooth j) j).continuousOn.mono hsub
  have hloc := gauss_local hP hn0 hr hM'0 hFa hψc (ℓ₀ + t • (ℓ₁ - ℓ₀)) hT
  have hρr : r / Real.sqrt n ≤ r := div_le_self hr.le (Real.one_le_sqrt.2 (by exact_mod_cast hn))
  have hBr : Metric.closedBall y (r / Real.sqrt n) ⊆ Metric.closedBall y r :=
    Metric.closedBall_subset_closedBall hρr
  have hlow := le_l2NormSq_of_chart (W₀.lerp W₁ t) dV hs j
    Metric.isClosed_closedBall.measurableSet (hBr.trans hball) hc.le
    (fun w hw => hdens w (hBr hw))
  have hpt : ptNormSq (W₀.lerp W₁ t) n s x = ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) := by
    rw [ptNormSq_eq_of_mem _ hs j hxj, hψy]
    simp [hF, y, e.left_inv hxj]
  have hmain : ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c ≤
      sectionL2NormSq (W₀.lerp W₁ t) dV n s := by
    rw [hpt]
    calc _ = c * (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ *
          gaussDiscMass M' r ^ D) := by ring
      _ ≤ c * ∫ w in Metric.closedBall y (r / Real.sqrt n), ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) :=
          mul_le_mul_of_nonneg_left hloc hc.le
      _ = _ := rfl
      _ ≤ _ := hlow
  have hl0 : 0 ≤ sectionL2NormSq (W₀.lerp W₁ t) dV n s := sectionL2NormSq_nonneg _ _ _ _
  rcases hl0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; positivity
  rw [div_le_iff₀ hpos]
  have hp0 : 0 ≤ ptNormSq (W₀.lerp W₁ t) n s x := ptNormSq_nonneg _ _ _ _
  calc ptNormSq (W₀.lerp W₁ t) n s x
      = (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D *
          (ptNormSq (W₀.lerp W₁ t) n s x * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M' r ^ D * c) := by
        field_simp
    _ ≤ (c * gaussDiscMass M' r ^ D)⁻¹ * (n : ℝ) ^ D * sectionL2NormSq (W₀.lerp W₁ t) dV n s :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
