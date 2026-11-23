import Mathlib
open Metric Filter Topology Set

namespace GlobalTheory.PuncturedDiscExtension

theorem analyticAt_update_of_bdd {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    (hb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B) :
    AnalyticAt ℂ (Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F)) 0 := by
  obtain ⟨B, hB⟩ := hb
  have ht : Tendsto F (𝓝[≠] (0:ℂ)) (𝓝 (limUnder (𝓝[≠] (0:ℂ)) F)) := by
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd
    refine isBoundedUnder_of_eventually_le (a := B + ‖F 0‖) ?_
    filter_upwards [hB] with z hz
    exact (norm_sub_le _ _).trans (by linarith)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · rw [eventually_nhdsWithin_iff] at hd ⊢
    filter_upwards [hd] with z hz hz0
    have heq : Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F) =ᶠ[𝓝 z] F := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hz hz0).congr_of_eventuallyEq heq
  · exact continuousAt_update_same.2 ht

theorem bdd_of_re_le {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    {M : ℝ} (hM : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z).re ≤ M) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B := by
  set g : ℂ → ℂ := fun z => (F z - ((M:ℂ) + 1))⁻¹ with hg
  have hre : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z - ((M:ℂ)+1)).re ≤ -1 := by
    filter_upwards [hM] with z hz
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hne : ∀ᶠ z in 𝓝[≠] (0:ℂ), F z - ((M:ℂ)+1) ≠ 0 := by
    filter_upwards [hre] with z hz h
    rw [h, Complex.zero_re] at hz
    linarith
  have hnorm : ∀ᶠ z in 𝓝[≠] (0:ℂ), 1 ≤ ‖F z - ((M:ℂ)+1)‖ := by
    filter_upwards [hre] with z hz
    have h1 := Complex.abs_re_le_norm (F z - ((M:ℂ)+1))
    have h2 : 1 ≤ |(F z - ((M:ℂ)+1)).re| := by
      rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hgd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g z := by
    filter_upwards [hd, hne] with z h1 h2
    exact (h1.sub_const _).inv h2
  have hgb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖g z‖ ≤ B := ⟨1, by
    filter_upwards [hnorm] with z hz
    simp only [hg, norm_inv]
    exact inv_le_one_of_one_le₀ hz⟩
  have ha := analyticAt_update_of_bdd hgd hgb
  set g' := Function.update g 0 (limUnder (𝓝[≠] (0:ℂ)) g) with hg'
  have hg'eq : ∀ z, z ≠ 0 → g' z = g z := fun z hz => Function.update_of_ne hz _ _
  by_cases hL : g' 0 = 0
  · exfalso
    rcases ha.eventually_constant_or_nhds_le_map_nhds with h | h
    · have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, hne, self_mem_nhdsWithin] with z h1 h2 h3
        rw [hg'eq z h3, hL] at h1
        exact inv_ne_zero h2 h1
      exact hF.exists.elim fun _ h => h
    · have hS : ∀ᶠ z in 𝓝 (0:ℂ), g' z = 0 ∨ ((g' z)⁻¹).re ≤ -1 := by
        have h0 := eventually_nhdsWithin_iff.1 hre
        filter_upwards [h0] with z hz
        by_cases hz0 : z = 0
        · left; rw [hz0]; exact hL
        · right; rw [hg'eq z hz0]; simp only [hg, inv_inv]; exact hz hz0
      have hS' : {w : ℂ | w = 0 ∨ (w⁻¹).re ≤ -1} ∈ 𝓝 (g' 0) := h hS
      rw [hL] at hS'
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS'
      have hmem : ((ε/2 : ℝ) : ℂ) ∈ ball (0:ℂ) ε := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      rcases hball hmem with h1 | h1
      · have : (ε/2 : ℝ) = 0 := by exact_mod_cast h1
        linarith
      · rw [← Complex.ofReal_inv, Complex.ofReal_re] at h1
        have : 0 < (ε/2)⁻¹ := inv_pos.2 (by linarith)
        linarith
  · have hpos : 0 < ‖g' 0‖ := norm_pos_iff.2 hL
    have hc : ContinuousAt g' 0 := ha.continuousAt
    have hev : ∀ᶠ z in 𝓝 (0:ℂ), ‖g' 0‖ / 2 < ‖g' z‖ :=
      hc.norm.eventually (lt_mem_nhds (by linarith))
    refine ⟨‖(M:ℂ)+1‖ + 2 / ‖g' 0‖, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin, hne] with z h1 h2 h3
    rw [hg'eq z h2] at h1
    have hq : 0 < ‖F z - ((M:ℂ)+1)‖ := norm_pos_iff.2 h3
    have hgz : ‖g z‖ = ‖F z - ((M:ℂ)+1)‖⁻¹ := by simp only [hg, norm_inv]
    rw [hgz] at h1
    have key : ‖F z - ((M:ℂ)+1)‖ ≤ 2 / ‖g' 0‖ := by
      have h4 := mul_lt_mul_of_pos_right h1 hq
      rw [inv_mul_cancel₀ hq.ne'] at h4
      rw [le_div_iff₀ hpos]
      nlinarith
    have h5 := norm_sub_norm_le (F z) ((M:ℂ)+1)
    linarith

end GlobalTheory.PuncturedDiscExtension

namespace GlobalTheory

open GlobalTheory.PuncturedDiscExtension in

theorem holomorphic_extension_of_exp_two_pi_I_bound :
    ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r →
      DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) →
      (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 →
        ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧
        ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t := by
  intro H r C N hr hH hC
  have hball : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∈ ball (0:ℂ) r ∧ z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0:ℂ) hr), self_mem_nhdsWithin]
      with z h1 h2
    exact ⟨h1, h2⟩
  have hHd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ H z := by
    filter_upwards [hball] with z hz
    exact hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz.1, hz.2⟩)
  set f : ℂ → ℂ := fun z => 2 * (Real.pi:ℂ) * Complex.I * H z with hf
  have hfd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z := by
    filter_upwards [hHd] with z hz
    exact hz.const_mul _
  have hfb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖f z‖ ≤ B := by
    set Gf : ℂ → ℂ := fun z => z ^ N * Complex.exp (f z) with hGf
    have hGd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ Gf z := by
      filter_upwards [hfd] with z hz
      exact (differentiableAt_id.pow N).mul hz.cexp
    have hGb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖Gf z‖ ≤ B := ⟨C, by
      filter_upwards [hball] with z hz
      have h := hC z hz.1 hz.2
      show ‖z ^ N * Complex.exp (f z)‖ ≤ C
      rw [norm_mul, norm_pow, mul_comm]
      exact h⟩
    have ha := analyticAt_update_of_bdd hGd hGb
    set G' := Function.update Gf 0 (limUnder (𝓝[≠] (0:ℂ)) Gf) with hG'
    have hG'eq : ∀ z, z ≠ 0 → G' z = Gf z := fun z hz => Function.update_of_ne hz _ _
    have hnz : ¬ ∀ᶠ z in 𝓝 (0:ℂ), G' z = 0 := by
      intro h
      have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z h1 h2
        rw [hG'eq z h2] at h1
        exact mul_ne_zero (pow_ne_zero _ h2) (Complex.exp_ne_zero _) h1
      exact hF.exists.elim fun _ h => h
    obtain ⟨k, u, hu, hu0, hGu⟩ := (ha.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnz
    have hpos : 0 < ‖u 0‖ := norm_pos_iff.2 hu0
    have huc : ContinuousAt u 0 := hu.continuousAt
    have hup : ∀ᶠ z in 𝓝 (0:ℂ), ‖u z‖ < ‖u 0‖ + 1 :=
      huc.norm.eventually (gt_mem_nhds (by linarith))
    have hlo : ∀ᶠ z in 𝓝 (0:ℂ), ‖u 0‖ / 2 < ‖u z‖ :=
      huc.norm.eventually (lt_mem_nhds (by linarith))
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖z‖ < 1 := by
      filter_upwards [ball_mem_nhds (0:ℂ) one_pos] with z hz
      simpa using hz
    have hrel : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ≠ 0 ∧ ‖z‖ < 1 ∧ ‖u z‖ < ‖u 0‖ + 1 ∧
        ‖u 0‖ / 2 < ‖u z‖ ∧ z ^ N * Complex.exp (f z) = z ^ k * u z := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h1.and (hup.and (hlo.and hGu)))]
        with z hz hh
      obtain ⟨ha1, ha2, ha3, ha4⟩ := hh
      refine ⟨hz, ha1, ha2, ha3, ?_⟩
      have := hG'eq z hz
      rw [ha4, sub_zero, smul_eq_mul] at this
      exact this.symm
    rcases le_or_gt N k with hk | hk
    · refine bdd_of_re_le hfd (M := Real.log (‖u 0‖ + 1)) ?_
      filter_upwards [hrel] with z hh
      obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
      have hk' : z ^ k = z ^ N * z ^ (k - N) := by rw [← pow_add, Nat.add_sub_cancel' hk]
      rw [hk', mul_assoc] at he
      have he2 : Complex.exp (f z) = z ^ (k - N) * u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
      have hn : ‖Complex.exp (f z)‖ ≤ ‖u 0‖ + 1 := by
        rw [he2, norm_mul, norm_pow]
        have : ‖z‖ ^ (k - N) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
        nlinarith [norm_nonneg (u z)]
      rw [Complex.norm_exp] at hn
      have := Real.log_le_log (Real.exp_pos _) hn
      rwa [Real.log_exp] at this
    · obtain ⟨B, hB⟩ := bdd_of_re_le (F := fun z => -f z)
        (by filter_upwards [hfd] with z hz; exact hz.neg) (M := -Real.log (‖u 0‖ / 2)) (by
        filter_upwards [hrel] with z hh
        obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
        have hN : z ^ N = z ^ k * z ^ (N - k) := by rw [← pow_add, Nat.add_sub_cancel' hk.le]
        rw [hN, mul_assoc] at he
        have he2 : z ^ (N - k) * Complex.exp (f z) = u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
        have hn : ‖u 0‖ / 2 ≤ ‖Complex.exp (f z)‖ := by
          have : ‖u z‖ ≤ ‖Complex.exp (f z)‖ := by
            rw [← he2, norm_mul, norm_pow]
            have : ‖z‖ ^ (N - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
            nlinarith [norm_nonneg (Complex.exp (f z))]
          linarith
        rw [Complex.norm_exp] at hn
        have := Real.log_le_log (by positivity) hn
        rw [Real.log_exp] at this
        simp only [Complex.neg_re]
        linarith)
      exact ⟨B, by filter_upwards [hB] with z hz; simpa only [norm_neg] using hz⟩
  obtain ⟨B, hB⟩ := hfb
  have hHb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖H z‖ ≤ B := ⟨B / (2 * Real.pi), by
    filter_upwards [hB] with z hz
    have hf' : ‖f z‖ = 2 * Real.pi * ‖H z‖ := by
      simp only [hf, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [hf'] at hz
    rw [le_div_iff₀ (by positivity)]
    linarith⟩
  have haH := analyticAt_update_of_bdd hHd hHb
  refine ⟨Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H), ?_,
    fun t _ ht => Function.update_of_ne ht _ _⟩
  intro z hz
  by_cases h0 : z = 0
  · subst h0
    exact haH.differentiableAt.differentiableWithinAt
  · have hzd : DifferentiableAt ℂ H z :=
      hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, h0⟩)
    have heq : Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H) =ᶠ[𝓝 z] H := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hzd.congr_of_eventuallyEq heq).differentiableWithinAt

end GlobalTheory
