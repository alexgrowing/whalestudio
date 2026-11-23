import Formalism.HermitianCurvature.LatticeHerglotzBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantIntegrals

open MeasureTheory Set Finset Function

noncomputable section

namespace Formalism.FourierDecayAlt.P.LatticeSummability

open Formalism.FourierDecayAlt.crystallineComparison

theorem mfac_nonneg (K : ℕ) {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (ha : 0 ≤ a) : 0 ≤ mfac K L a := by
  unfold mfac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (by positivity)

theorem mfac_anti (K : ℕ) {L : ℝ} (hL : 0 < L) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    mfac K L b' ≤ mfac K L b := by
  unfold mfac
  by_cases hb0 : b = 0
  · rw [if_pos hb0]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hb'0 : b' ≠ 0 := by linarith
    rw [if_neg hb0, if_neg hb'0]
    refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hL.le (by linarith)) ?_ K)
    exact div_le_div_of_nonneg_left hL.le hbpos hbb

theorem mfac_shift (K : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    mfac K L a ≤ mfac K (L + δ) (a + δ) := by
  unfold mfac
  have had : a + δ ≠ 0 := by linarith
  rw [if_neg had]
  have hone : ∀ {x : ℝ}, 1 ≤ x → min 1 (x ^ K) = 1 := fun hx => min_eq_left (one_le_pow₀ hx)
  rcases le_or_gt L a with hLa | hLa
  · have ha0 : a ≠ 0 := by linarith
    rw [if_neg ha0]
    have hapos : 0 < a := by linarith
    refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hL.le hapos.le) ?_ K)
    rw [div_le_div_iff₀ hapos (by linarith)]
    nlinarith
  · have h1 : 1 ≤ (L + δ) / (a + δ) := (one_le_div (by linarith : (0 : ℝ) < a + δ)).mpr (by linarith)
    rw [hone h1]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _

private theorem mfac_le_one_add_pow_mul_rpow_neg (K : ℕ) {M a : ℝ} (hM : 0 < M) (ha : 0 ≤ a) :
    mfac K M a ≤ (1 + M) ^ K * (1 + a) ^ (-(K : ℝ)) := by
  have h1a : 0 < 1 + a := by linarith
  rw [Real.rpow_neg h1a.le, Real.rpow_natCast, ← div_eq_mul_inv, ← div_pow]
  unfold mfac
  split_ifs with h0
  · subst h0
    simp only [add_zero, div_one]
    exact one_le_pow₀ (by linarith)
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rcases le_or_gt a M with haM | haM
    · exact (min_le_left _ _).trans (one_le_pow₀ ((one_le_div h1a).mpr (by linarith)))
    · refine (min_le_right _ _).trans (pow_le_pow_left₀ (div_nonneg hM.le hapos.le) ?_ K)
      rw [div_le_div_iff₀ hapos h1a]
      nlinarith

theorem latticeSummable : LatticeSummable := by
  intro f K L La _ hK hL
  classical
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ σ : La, σ ≠ 0 → r ≤ ‖(σ : V f)‖ := by
    have h0 : IsOpen ({0} : Set La) := isOpen_discrete _
    rw [Metric.isOpen_iff] at h0
    obtain ⟨r, hr, hsub⟩ := h0 0 rfl
    refine ⟨r, hr, fun σ hσ => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hmem : σ ∈ Metric.ball (0 : La) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hlt
    exact hσ (hsub hmem)
  set δ := r / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hnn : ∀ σ : V f, 0 ≤ mL K L σ := fun σ =>
    Finset.prod_nonneg fun v _ => mfac_nonneg K (hL v).le _ (norm_nonneg _)
  have hdom : ∀ σ z : V f, dist z σ < δ → mL K L σ ≤ mL K (fun v => L v + δ) z := by
    intro σ z hz
    unfold mL
    apply Finset.prod_le_prod (fun v _ => mfac_nonneg K (hL v).le _ (norm_nonneg _))
    intro v _
    have h1 : ‖z v‖ ≤ ‖σ v‖ + δ := by
      have h3 := norm_le_pi_norm (z - σ) v
      have h2 : ‖z v‖ ≤ ‖σ v‖ + ‖(z - σ) v‖ := by
        calc ‖z v‖ = ‖σ v + (z - σ) v‖ := by simp
          _ ≤ _ := norm_add_le _ _
      rw [dist_eq_norm] at hz
      linarith
    calc mfac K (L v) ‖σ v‖ ≤ mfac K (L v + δ) (‖σ v‖ + δ) := mfac_shift K (hL v) hδ0 (norm_nonneg _)
      _ ≤ mfac K (L v + δ) ‖z v‖ := mfac_anti K (by linarith [hL v]) (norm_nonneg _) h1
  have hint : Integrable (fun z : V f => mL K (fun v => L v + δ) z) := by
    have h1 : ∀ v, Integrable (fun l : ℂ => mfac K (L v + δ) ‖l‖) := by
      intro v
      have hM0 : 0 < L v + δ := by linarith [hL v]
      have hg : Integrable (fun l : ℂ => (1 + (L v + δ)) ^ K * (1 + ‖l‖) ^ (-(K : ℝ))) :=
        (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; exact_mod_cast hK)).const_mul _
      refine hg.mono' ?_ (Filter.Eventually.of_forall fun l => ?_)
      · have hmeas : Measurable (fun l : ℂ => mfac K (L v + δ) ‖l‖) := by
          unfold mfac
          exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const) measurable_const
            (by fun_prop)
        exact hmeas.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mfac_nonneg K hM0.le _ (norm_nonneg _))]
        exact mfac_le_one_add_pow_mul_rpow_neg K hM0 (norm_nonneg _)
    have := Integrable.fintype_prod (f := fun v (l : ℂ) => mfac K (L v + δ) ‖l‖)
      (μ := fun _ => (volume : Measure ℂ)) h1
    rw [← volume_pi] at this
    exact this
  have hIt := hint.lintegral_lt_top
  refine summable_of_sum_le (c := (∫⁻ z, ENNReal.ofReal (mL K (fun v => L v + δ) z)).toReal /
    (volume (Metric.ball (0 : V f) δ)).toReal) (fun σ => hnn σ) ?_
  intro F
  have hB0 : 0 < volume (Metric.ball (0 : V f) δ) := Metric.measure_ball_pos _ _ hδ0
  have hBt : volume (Metric.ball (0 : V f) δ) < ⊤ := measure_ball_lt_top
  have hkey : volume (Metric.ball (0 : V f) δ) * ∑ σ ∈ F, ENNReal.ofReal (mL K L (σ : V f)) ≤
      ∫⁻ z, ENNReal.ofReal (mL K (fun v => L v + δ) z) := by
    rw [Finset.mul_sum]
    calc ∑ σ ∈ F, volume (Metric.ball (0 : V f) δ) * ENNReal.ofReal (mL K L (σ : V f))
        = ∑ σ ∈ F, ∫⁻ _z in Metric.ball (σ : V f) δ, ENNReal.ofReal (mL K L (σ : V f)) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [setLIntegral_const, Measure.addHaar_ball_center volume (σ : V f) δ]
          ring
      _ ≤ ∑ σ ∈ F, ∫⁻ z in Metric.ball (σ : V f) δ, ENNReal.ofReal (mL K (fun v => L v + δ) z) :=
          Finset.sum_le_sum fun σ _ => setLIntegral_mono' measurableSet_ball fun z hz =>
            ENNReal.ofReal_le_ofReal (hdom _ _ hz)
      _ = ∫⁻ z in ⋃ σ ∈ F, Metric.ball (σ : V f) δ, ENNReal.ofReal (mL K (fun v => L v + δ) z) := by
          rw [lintegral_biUnion_finset]
          · intro σ _ σ' _ hne
            apply Metric.ball_disjoint_ball
            have h4 := hball (σ - σ') (sub_ne_zero.mpr hne)
            rw [dist_eq_norm]
            have h5 : ((σ - σ' : La) : V f) = (σ : V f) - σ' := rfl
            rw [h5] at h4
            linarith
          · intro σ _
            exact measurableSet_ball
      _ ≤ _ := setLIntegral_le_lintegral _ _
  rw [← ENNReal.ofReal_sum_of_nonneg (f := fun σ : La => mL K L (σ : V f)) fun σ _ => hnn σ] at hkey
  have h6 := ENNReal.toReal_mono hIt.ne hkey
  have hs0 : 0 ≤ ∑ σ ∈ F, mL K L (σ : V f) := Finset.sum_nonneg fun σ _ => hnn _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs0] at h6
  rw [le_div_iff₀ (ENNReal.toReal_pos hB0.ne' hBt.ne), mul_comm]
  exact h6

end Formalism.FourierDecayAlt.P.LatticeSummability

theorem Formalism.FourierDecayAlt.P.latticeSummable_statement : Formalism.FourierDecayAlt.crystallineComparison.LatticeSummable := LatticeSummability.latticeSummable
