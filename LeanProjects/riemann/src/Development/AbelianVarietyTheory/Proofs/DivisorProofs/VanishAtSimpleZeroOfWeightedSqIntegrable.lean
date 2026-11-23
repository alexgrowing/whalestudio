import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem vanish_at_simple_zero_of_weighted_sq_integrable :
    ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O →
      DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O →
      ∀ u : V n → ℂ, ContinuousOn u O →
        ∫⁻ v in O, ENNReal.ofReal (‖u v‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) < ⊤ →
        u p = 0 := by
  intro n hn1 p O Z lam hO hpO hZ hZ0 hdet hlam u hu hint
  have hn : 0 < n := hn1
  by_contra hne
  have hOn : O ∈ 𝓝 p := hO.mem_nhds hpO

  have htr : Tendsto (fun z : V n => z + p) (𝓝 0) (𝓝 p) := by
    have := (continuous_add_right p).tendsto (0 : V n)
    simpa using this
  set a := ‖u p‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne
  have ev1 : ∀ᶠ z in 𝓝 (0 : V n), a / 2 < ‖u (z + p)‖ := by
    have hc : Tendsto (fun v => ‖u v‖) (𝓝 p) (𝓝 a) := ((hu.continuousAt hOn).norm)
    exact htr.eventually (hc.eventually (Ioi_mem_nhds (by linarith)))
  have ev4 : ∀ᶠ z in 𝓝 (0 : V n), lam p - 1 < lam (z + p) := by
    have hc : Tendsto lam (𝓝 p) (𝓝 (lam p)) := hlam.continuousAt hOn
    exact htr.eventually (hc.eventually (Ioi_mem_nhds (by linarith)))
  have ev5 : ∀ᶠ z in 𝓝 (0 : V n), z + p ∈ O := htr.eventually hOn
  set σ : V n → V n := fun z => Z (z + p) with hσ
  have hσ0 : σ 0 = 0 := by simp [hσ, hZ0]
  have hσd : fderiv ℂ σ 0 = fderiv ℂ Z p := by
    rw [hσ, fderiv_comp_add_right]; simp
  obtain ⟨c, hc, ev2⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.lower_of_det hn hσ0 (hσd ▸ hdet)
  have hdiff : DifferentiableAt ℂ σ 0 := by
    have h1 : DifferentiableAt ℂ Z (0 + p) := by simpa using hZ.differentiableAt hOn
    exact h1.comp (0 : V n) ((differentiableAt_id).add_const p)
  obtain ⟨C, ev3⟩ : ∃ C : ℝ, ∀ᶠ z in 𝓝 (0 : V n), ‖σ z‖ ≤ C * ‖z‖ := by
    have h := hdiff.hasFDerivAt.isBigO_sub
    simp only [hσ0, sub_zero] at h
    obtain ⟨C, hC⟩ := h.bound
    exact ⟨C, hC⟩
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp
    (ev1.and (ev2.and (ev3.and (ev4.and ev5))))
  set Eb : ℝ := Real.exp (1 - lam p) with hEb
  set B : ℝ := C ^ 2 * Eb + 1 with hB
  have hB0 : 0 < B := by positivity
  set K : ℝ := (a / 2) ^ 2 * B ^ (-(n : ℝ)) with hK
  have hK0 : 0 < K := by positivity
  have hp : -(n : ℝ) ≤ 0 := by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _; linarith
  set F : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (‖u v‖ ^ 2 *
    Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) with hF
  have hpt : ∀ z ∈ ball (0 : V n) δ0, z ≠ 0 →
      ENNReal.ofReal K * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤ F (z + p) := by
    intro z hz hz0
    obtain ⟨h1, h2, h3, h4, -⟩ := hall (by simpa using hz)
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    set X := ‖Z (z + p)‖ ^ 2 * Real.exp (-lam (z + p)) with hX
    have hZpos : 0 < ‖Z (z + p)‖ := lt_of_lt_of_le (by positivity) h2
    have hXpos : 0 < X := by positivity
    have hexle : Real.exp (-lam (z + p)) ≤ Eb := Real.exp_le_exp.mpr (by linarith)
    have hXle : X ≤ B * ‖z‖ ^ 2 := by
      have hZle : ‖Z (z + p)‖ ^ 2 ≤ C ^ 2 * ‖z‖ ^ 2 := by
        have h0 : 0 ≤ C * ‖z‖ := le_trans (norm_nonneg _) h3
        calc ‖Z (z + p)‖ ^ 2 ≤ (C * ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
          _ = C ^ 2 * ‖z‖ ^ 2 := by ring
      calc X ≤ (C ^ 2 * ‖z‖ ^ 2) * Eb :=
            mul_le_mul hZle hexle (Real.exp_pos _).le (by positivity)
        _ ≤ B * ‖z‖ ^ 2 := by rw [hB]; nlinarith [sq_nonneg ‖z‖, sq_nonneg C, Real.exp_pos (1 - lam p)]
    have hw : Real.exp (-((n : ℝ) * Real.log X)) = X ^ (-(n : ℝ)) := by
      rw [Real.rpow_def_of_pos hXpos]; ring_nf
    show ENNReal.ofReal K * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
      ENNReal.ofReal (‖u (z + p)‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log X)))
    rw [hw, ← ENNReal.ofReal_mul hK0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hSp : (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) ≤ X ^ (-(n : ℝ)) := Real.rpow_le_rpow_of_nonpos hXpos hXle hp
    have hexp : (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) = B ^ (-(n : ℝ)) * ‖z‖ ^ (-2 * (n : ℝ)) := by
      rw [Real.mul_rpow hB0.le (by positivity), ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
      ring_nf
    have hu2 : (a / 2) ^ 2 ≤ ‖u (z + p)‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    calc K * ‖z‖ ^ (-2 * (n : ℝ)) = (a / 2) ^ 2 * (B * ‖z‖ ^ 2) ^ (-(n : ℝ)) := by rw [hexp, hK]; ring
      _ ≤ ‖u (z + p)‖ ^ 2 * X ^ (-(n : ℝ)) :=
        mul_le_mul hu2 hSp (by positivity) (by positivity)
  have hne0 : ∀ᵐ z ∂(volume : Measure (V n)), z ≠ 0 := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)

  have hsubO : ∀ z ∈ ball (0 : V n) δ0, z + p ∈ O := fun z hz => (hall (by simpa using hz)).2.2.2.2
  have htrans : ∫⁻ z in ball (0 : V n) δ0, F (z + p) ≤ ∫⁻ v in O, F v := by
    have hind : ∀ z : V n, (ball p δ0).indicator F (z + p) = (ball (0 : V n) δ0).indicator (fun z => F (z + p)) z := by
      intro z
      have hm : z + p ∈ ball p δ0 ↔ z ∈ ball (0 : V n) δ0 := by
        simp [mem_ball, dist_eq_norm]
      by_cases hz : z ∈ ball (0 : V n) δ0
      · rw [Set.indicator_of_mem (hm.mpr hz), Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem (fun h => hz (hm.mp h)), Set.indicator_of_notMem hz]
    have e1 : ∫⁻ z in ball (0 : V n) δ0, F (z + p) = ∫⁻ v in ball p δ0, F v := by
      rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
      simp_rw [← hind]
      exact lintegral_add_right_eq_self (μ := volume) ((ball p δ0).indicator F) p
    have hsb : ball p δ0 ⊆ O := by
      intro v hv
      have h1 : v - p ∈ ball (0 : V n) δ0 := by simpa [mem_ball, dist_eq_norm] using hv
      simpa using hsubO (v - p) h1
    rw [e1]
    exact lintegral_mono_set hsb
  have hlow : ENNReal.ofReal K * ∫⁻ z in ball (0 : V n) δ0, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
      ∫⁻ v in O, F v := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ htrans
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne0] with z hz hz0
    exact hpt z hz hz0
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div hn hδ0, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hK0).ne'] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end

end GlobalTheory
