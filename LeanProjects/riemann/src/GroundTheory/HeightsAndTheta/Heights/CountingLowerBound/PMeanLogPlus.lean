import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology Set

noncomputable section

universe u

theorem lt_max_zero_log_div_iff {t r l : ℝ} (ht : 0 < t) (hr : 0 < r) (hl : 0 < l) :
    t < max 0 (log (r / l)) ↔ l < exp (-t) * r := by
  rw [lt_max_iff, lt_log_iff_exp_lt (div_pos hr hl), lt_div_iff₀ hl, exp_neg,
    ← div_eq_inv_mul, lt_div_iff₀ (exp_pos t), mul_comm l]
  constructor
  · rintro (h | h)
    · exact absurd h (not_lt.2 ht.le)
    · exact h
  · exact Or.inr

theorem log_two_mul_pow_div_add_le {a : ℕ} {k : ℝ} (ha : 1 ≤ a) (hk : 3 * (a : ℝ) ≤ k) :
    log (2 * 36 ^ a) / k + 1 / k ≤ 3 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hk0 : 0 < k := by linarith
  have h2 : log 2 < 1 := by have := log_two_lt_d9; norm_num at this; linarith
  have h36 : log 36 < 4 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have he : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
    have h := pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [he]; norm_num at h ⊢; linarith
  have hlog : log (2 * 36 ^ a) = log 2 + a * log 36 := by
    rw [log_mul (by norm_num) (by positivity), log_pow]
  rw [← add_div, div_le_iff₀ hk0, hlog]
  nlinarith

theorem MeanLogPlus.proof (h1 : TailBound.Statement.{u}) : MeanLogPlus.Statement.{u} := by
  intro X _ μ lam cnt a ka r h
  have := h.isProbability
  have hk0 : 0 < ka := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast h.one_le_a
    linarith [h.three_a_le_ka]
  set F : X → ℝ := fun z => max 0 (log (r / lam z)) with hF
  have hFm : Measurable F :=
    measurable_const.max (measurable_log.comp (measurable_const.div h.lam_meas))
  have hF0 : ∀ z, 0 ≤ F z := fun z => le_max_left _ _
  set C : ℝ := 2 * 36 ^ a with hC
  have hC1 : 1 ≤ C := by rw [hC]; have : (1 : ℝ) ≤ 36 ^ a := one_le_pow₀ (by norm_num); linarith
  set x0 : ℝ := log C / ka with hx0
  have hx00 : 0 ≤ x0 := div_nonneg (log_nonneg hC1) hk0.le
  set g : ℝ → ℝ := fun t => min 1 (C * exp (-ka * t)) with hg

  have hpt : ∀ t ∈ Ioi (0 : ℝ), μ {z | t < F z} ≤ ENNReal.ofReal (g t) := by
    intro t ht
    have hset : {z | t < F z} = {z | lam z < exp (-t) * r} := by
      ext z; exact lt_max_zero_log_div_iff ht h.r_pos (h.lam_pos z)
    rw [hset, ← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    have := h1 X μ lam cnt a ka r h t (le_of_lt ht)
    simpa [hg, neg_mul] using this

  have hexp : IntegrableOn (fun t => C * exp (-ka * t)) (Ioi x0) :=
    (exp_neg_integrableOn_Ioi x0 hk0).const_mul C
  have hint : ∫ t in Ioi x0, C * exp (-ka * t) = 1 / ka := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x0]
    have : exp (-ka * x0) = C⁻¹ := by
      rw [hx0, show -ka * (log C / ka) = -log C by field_simp, exp_neg,
        exp_log (by linarith)]
    rw [this]; field_simp
  have hL : ∫⁻ z, ENNReal.ofReal (F z) ∂μ ≤ ENNReal.ofReal 3 := by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hF0) hFm.aemeasurable]
    calc ∫⁻ t in Ioi 0, μ {z | t < F z}
        ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (g t) := setLIntegral_mono' measurableSet_Ioi hpt
      _ ≤ ∫⁻ t in Ioc 0 x0 ∪ Ioi x0, ENNReal.ofReal (g t) := by
          rw [Ioc_union_Ioi_eq_Ioi hx00]
      _ ≤ (∫⁻ t in Ioc 0 x0, ENNReal.ofReal (g t)) + ∫⁻ t in Ioi x0, ENNReal.ofReal (g t) :=
          lintegral_union_le _ _ _
      _ ≤ (∫⁻ t in Ioc 0 x0, 1) + ∫⁻ t in Ioi x0, ENNReal.ofReal (C * exp (-ka * t)) :=
          add_le_add (lintegral_mono fun t => ENNReal.ofReal_le_one.2 (min_le_left _ _))
            (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ = ENNReal.ofReal x0 + ENNReal.ofReal (1 / ka) := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero, ← hint,
            ofReal_integral_eq_lintegral_ofReal hexp
              (ae_of_all _ fun t => by positivity)]
      _ = ENNReal.ofReal (x0 + 1 / ka) := (ENNReal.ofReal_add hx00 (by positivity)).symm
      _ ≤ ENNReal.ofReal 3 :=
          ENNReal.ofReal_le_ofReal (log_two_mul_pow_div_add_le h.one_le_a h.three_a_le_ka)
  have hInt : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hF0)]
    exact lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hFm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL

end

end GroundTheory.Heights₂.Heights.LowerBound
