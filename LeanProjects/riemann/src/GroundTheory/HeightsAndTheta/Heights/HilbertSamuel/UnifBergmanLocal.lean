import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem le_l2NormSq_of_chart [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (W : Weight L)
    (dV : SmoothVolume A) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (j : Fin A.n)
    {B : Set (Fin D → ℂ)} (hB : MeasurableSet B) (hBt : B ⊆ (A.chart j).target) {c : ℝ}
    (hc : 0 ≤ c) (hdens : ∀ y ∈ B, c ≤ dV.dens j y) :
    c * ∫ y in B, ‖s j ((A.chart j).symm y)‖ ^ 2 *
        Real.exp (-(n : ℝ) * W.φ j ((A.chart j).symm y)) ≤ sectionL2NormSq W dV n s := by
  have := dV.isProb
  set P := ptNormSq W n s with hPdef
  have hPc : Continuous P := continuous_ptNormSq W hs
  have hP0 : ∀ x, 0 ≤ P x := ptNormSq_nonneg W n s
  have hPi : Integrable P dV.μ := integrable_ptNormSq W dV hs
  have hl0 : 0 ≤ sectionL2NormSq W dV n s := integral_nonneg hP0
  set h : (Fin D → ℂ) → ℝ := fun y => ‖s j ((A.chart j).symm y)‖ ^ 2 *
    Real.exp (-(n : ℝ) * W.φ j ((A.chart j).symm y)) with hh
  have hPh : ∀ y ∈ B, P ((A.chart j).symm y) = h y := fun y hy =>
    ptNormSq_eq_of_mem W hs j ((A.chart j).map_target (hBt hy))
  have hh0 : ∀ y, 0 ≤ h y := fun y => by rw [hh]; positivity
  rw [← integral_const_mul]
  by_cases hi : Integrable (fun y => c * h y) (volume.restrict B)
  swap
  · rw [integral_undef hi]; exact hl0
  rw [← ENNReal.ofReal_le_ofReal_iff hl0, ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun y => mul_nonneg hc (hh0 y)), sectionL2NormSq,
    ofReal_integral_eq_lintegral_ofReal hPi (ae_of_all _ hP0)]
  calc ∫⁻ y in B, ENNReal.ofReal (c * h y)
      ≤ ∫⁻ y in B, ENNReal.ofReal (P ((A.chart j).symm y)) * ENNReal.ofReal (dV.dens j y) := by
        refine setLIntegral_mono' hB fun y hy => ?_
        rw [hPh y hy, ← ENNReal.ofReal_mul (hh0 y), mul_comm c]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hdens y hy) (hh0 y))
    _ ≤ ∫⁻ y in (A.chart j).target, ENNReal.ofReal (P ((A.chart j).symm y)) *
          ENNReal.ofReal (dV.dens j y) := lintegral_mono_set hBt
    _ = ∫⁻ x in (A.chart j).source, ENNReal.ofReal (P x) ∂dV.μ :=
        (dV.chart_lintegral j _ hPc.measurable.ennreal_ofReal).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (P x) ∂dV.μ := setLIntegral_le_lintegral _ _

lemma setIntegral_closedBall_add (y : Fin D → ℂ) (ρ : ℝ) (H : (Fin D → ℂ) → ℝ) :
    ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ, H (y + z) =
      ∫ w in Metric.closedBall y ρ, H w := by
  rw [← integral_indicator Metric.isClosed_closedBall.measurableSet,
    ← integral_indicator Metric.isClosed_closedBall.measurableSet]
  have e : (Metric.closedBall (0 : Fin D → ℂ) ρ).indicator (fun z => H (y + z)) =
      fun z => (Metric.closedBall y ρ).indicator H (y + z) := by
    funext z
    simp [Set.indicator, Metric.mem_closedBall, dist_eq_norm]
  rw [e, integral_add_left_eq_self]

theorem gauss_local (hP : PolydiscSubmean.Statement) {n : ℕ} (hn : 0 < n) {r M : ℝ} (hr : 0 < r)
    (hM : 0 ≤ M) {y : Fin D → ℂ} {F : (Fin D → ℂ) → ℂ} {ψ : (Fin D → ℂ) → ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall y r)) (hψ : ContinuousOn ψ (Metric.closedBall y r))
    (ℓ : (Fin D → ℂ) →L[ℝ] ℝ)
    (hT : ∀ z : Fin D → ℂ, ‖z‖ ≤ r → ψ (y + z) ≤ ψ y + ℓ z + M * ∑ i, ‖z i‖ ^ 2) :
    ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D ≤
      ∫ w in Metric.closedBall y (r / Real.sqrt n), ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
  set ρ := r / Real.sqrt n with hρ
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hρr : ρ ≤ r := div_le_self hr.le hsq
  have hρ0 : 0 ≤ ρ := div_nonneg hr.le (Real.sqrt_nonneg _)
  set ℓc : StrongDual ℂ (Fin D → ℂ) := StrongDual.extendRCLike ℓ with hℓc
  have hre : ∀ z, (ℓc z).re = ℓ z := fun z => by
    rw [hℓc]; exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) ℓ z
  set f : (Fin D → ℂ) → ℂ := fun z => F (y + z) * Complex.exp (-(n : ℂ) * ℓc z / 2) with hf
  have hyz : ∀ z : Fin D → ℂ, ‖z‖ ≤ r → y + z ∈ Metric.closedBall y r := fun z hz => by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall 0 (r / Real.sqrt n)) := by
    intro z hz
    have hz' : ‖z‖ ≤ r := (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr
    have h1 : AnalyticAt ℂ (fun z : Fin D → ℂ => F (y + z)) z :=
      (hF (y + z) (hyz z hz')).comp (analyticAt_const.add analyticAt_id)
    have h2 : AnalyticAt ℂ (fun z : Fin D → ℂ => Complex.exp (-(n : ℂ) * ℓc z / 2)) z :=
      ((analyticAt_const.mul (ℓc.analyticAt z)).div_const).cexp
    exact h1.mul h2
  have hnorm : ∀ z, ‖f z‖ ^ 2 = ‖F (y + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z) := fun z => by
    have : (-(n : ℂ) * ℓc z / 2).re = -(n : ℝ) * ℓ z / 2 := by
      rw [← hre z]; simp [Complex.mul_re]
    rw [hf, norm_mul, Complex.norm_exp, this, mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hf0 : f 0 = F y := by simp [hf]
  have key := hP D n (fun _ => M) r f hn hr (fun _ => hM) hfa
  rw [hf0, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at key

  set H : (Fin D → ℂ) → ℝ := fun w => ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) with hH
  have hHc : ContinuousOn H (Metric.closedBall y r) := by
    refine (hF.continuousOn.norm.pow 2).mul ?_
    exact (continuousOn_const.mul hψ).rexp
  have hHi : IntegrableOn (fun z => Real.exp ((n : ℝ) * ψ y) * H (y + z))
      (Metric.closedBall (0 : Fin D → ℂ) ρ) := by
    refine ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) ?_
    refine continuousOn_const.mul (hHc.comp (continuousOn_const.add continuousOn_id) ?_)
    intro z hz
    exact hyz z ((by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr)
  have hmono : ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ,
      ‖f z‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, M * ‖z j‖ ^ 2) ≤
      ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ, Real.exp ((n : ℝ) * ψ y) * H (y + z) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) hHi ?_
    refine (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).2 (ae_of_all _ fun z hz => ?_)
    have hz' : ‖z‖ ≤ r := (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr
    have hTz := hT z hz'
    dsimp only
    rw [hnorm, hH]
    dsimp only
    rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    rw [← Finset.mul_sum]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hTz hn0]
  rw [setIntegral_closedBall_add y ρ (fun w => Real.exp ((n : ℝ) * ψ y) * H w),
    integral_const_mul] at hmono
  have hchain := key.trans hmono
  have he : Real.exp (-(n : ℝ) * ψ y) * Real.exp ((n : ℝ) * ψ y) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D
      = Real.exp (-(n : ℝ) * ψ y) * (‖F y‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D) := by
        ring
    _ ≤ Real.exp (-(n : ℝ) * ψ y) * (Real.exp ((n : ℝ) * ψ y) *
          ∫ w in Metric.closedBall y ρ, H w) :=
        mul_le_mul_of_nonneg_left hchain (Real.exp_pos _).le
    _ = ∫ w in Metric.closedBall y ρ, H w := by rw [← mul_assoc, he, one_mul]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
