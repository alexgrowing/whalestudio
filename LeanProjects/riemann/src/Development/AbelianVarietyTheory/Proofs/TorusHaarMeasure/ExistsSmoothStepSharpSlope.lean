import Mathlib

open MeasureTheory Set
open scoped ContDiff

namespace GlobalTheory

theorem exists_smooth_step_sharp_slope (ρ ε : ℝ) (hε : 0 < ε) (h4 : 4 * ε < ρ) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ u, u ≤ ε → η u = 1) ∧ (∀ u, ρ - ε ≤ u → η u = 0) ∧
      (∀ u, 0 ≤ η u) ∧ (∀ u, η u ≤ 1) ∧ ∀ u, -(1 / (ρ - 4 * ε)) ≤ deriv η u := by
  let ψ : ContDiffBump (ρ / 2 : ℝ) := ⟨ρ / 2 - 2 * ε, ρ / 2 - ε, by linarith, by linarith⟩
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ t, t ≤ ε ∨ ρ - ε ≤ t → ψ t = 0 := by
    intro t ht
    apply ψ.zero_of_le_dist
    rw [Real.dist_eq]
    show ρ / 2 - ε ≤ |t - ρ / 2|
    rcases ht with ht | ht
    · rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
    · exact le_trans (by linarith) (le_abs_self _)
  have hψ1 : ∀ t, 2 * ε ≤ t → t ≤ ρ - 2 * ε → ψ t = 1 := by
    intro t h1 h2
    apply ψ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |t - ρ / 2| ≤ ρ / 2 - 2 * ε
    rw [abs_le]; constructor <;> linarith
  have hII : ∀ a b, IntervalIntegrable ψ volume a b := fun a b => hψc.intervalIntegrable a b
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun u => ∫ t in ε..u, ψ t := ⟨_, rfl⟩
  have hFd : ∀ u, HasDerivAt F (ψ u) u := by
    intro u; rw [hF]; exact (hψc.integral_hasStrictDerivAt ε u).hasDerivAt
  have hFs : ContDiff ℝ ∞ F := by
    refine contDiff_infty_iff_deriv.2 ⟨fun u => (hFd u).differentiableAt, ?_⟩
    have h : deriv F = ψ := funext fun u => (hFd u).deriv
    rw [h]; exact ψ.contDiff
  have hFlow : ∀ u, u ≤ ε → F u = 0 := by
    intro u hu
    rw [hF]
    show ∫ t in ε..u, ψ t = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      exact hψ0 t (Or.inl (le_trans ht.2 (sup_le le_rfl hu)))
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ t in ε..(ρ - ε), ψ t := ⟨_, rfl⟩
  have hFhigh : ∀ u, ρ - ε ≤ u → F u = I := by
    intro u hu
    rw [hF, hI]
    show ∫ t in ε..u, ψ t = ∫ t in ε..(ρ - ε), ψ t
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII ε (ρ - ε)) (hII (ρ - ε) u),
      intervalIntegral.integral_congr (a := ρ - ε) (b := u) (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      exact hψ0 t (Or.inr (le_trans (le_inf le_rfl hu) ht.1))
  have hIge : ρ - 4 * ε ≤ I := by
    rw [hI]
    calc ρ - 4 * ε = ∫ _ in (2 * ε)..(ρ - 2 * ε), (1 : ℝ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring
      _ = ∫ t in (2 * ε)..(ρ - 2 * ε), ψ t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le (by linarith)] at ht
          exact (hψ1 t ht.1 ht.2).symm
      _ ≤ ∫ t in ε..(ρ - ε), ψ t :=
          intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
            (Filter.Eventually.of_forall fun t => ψ.nonneg) (hII _ _)
  have hIpos : 0 < I := by linarith
  have hFrange : ∀ u, 0 ≤ F u ∧ F u ≤ I := by
    intro u
    rcases le_total u ε with h | h
    · rw [hFlow u h]; exact ⟨le_rfl, hIpos.le⟩
    rcases le_total (ρ - ε) u with h' | h'
    · rw [hFhigh u h']; exact ⟨hIpos.le, le_rfl⟩
    have hsplit : F u + ∫ t in u..(ρ - ε), ψ t = I := by
      rw [hF, hI]; exact intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)
    have h1 : 0 ≤ F u := by
      rw [hF]; exact intervalIntegral.integral_nonneg h fun t _ => ψ.nonneg
    have h2 : 0 ≤ ∫ t in u..(ρ - ε), ψ t := intervalIntegral.integral_nonneg h' fun t _ => ψ.nonneg
    exact ⟨h1, by linarith⟩
  refine ⟨fun u => 1 - F u / I, contDiff_const.sub (hFs.div_const I), ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; simp [hFlow u hu]
  · intro u hu; simp [hFhigh u hu, hIpos.ne']
  · intro u
    rw [sub_nonneg, div_le_one hIpos]; exact (hFrange u).2
  · intro u
    have : 0 ≤ F u / I := div_nonneg (hFrange u).1 hIpos.le
    linarith
  · intro u
    have hd : HasDerivAt (fun u => 1 - F u / I) (-(ψ u / I)) u :=
      ((hFd u).div_const I).const_sub 1
    rw [hd.deriv, neg_le_neg_iff, div_le_div_iff₀ hIpos (by linarith)]
    nlinarith [ψ.le_one (x := u), ψ.nonneg (x := u)]

theorem exists_cutoff_log_sharp : ∀ ρ0 θ : ℝ, 0 < ρ0 → 1 < θ → ∃ ε C : ℝ, 0 < ε ∧ ε < ρ0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ g : ℝ → ℝ,
    ContDiffOn ℝ ∞ g (Set.Ioi (-δ)) ∧ (∀ u, ρ0 - ε ≤ u → g u = 0) ∧
    (∀ u, 0 ≤ u → g u ≤ 0 ∧ 0 ≤ deriv g u ∧ -(θ / ρ0) ≤ deriv g u + u * deriv (deriv g) u) ∧
    (∀ u, 0 ≤ u → u ≤ ε → g u ≤ Real.log (u + δ) + C) ∧ ∀ u, ε / 2 ≤ u → -C ≤ g u := by
  intro ρ0 θ hρ hθ
  obtain ⟨ε, hε, hE⟩ : ∃ ε : ℝ, 0 < ε ∧ 8 * θ * ε = ρ0 * (θ - 1) :=
    ⟨ρ0 * (θ - 1) / (8 * θ), div_pos (mul_pos hρ (by linarith)) (by linarith), by field_simp⟩
  have h4 : 4 * ε < ρ0 := by nlinarith
  have hpos : 0 < ρ0 - 4 * ε := by linarith
  have hslope : 1 / (ρ0 - 4 * ε) ≤ θ / ρ0 := by
    rw [one_div_le hpos (by positivity), one_div_div, div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨η, hηs, hη1, hη0, hηnn, hηle, hηd⟩ := exists_smooth_step_sharp_slope ρ0 ε hε h4
  refine ⟨ε, 2 * ρ0 / ε + |Real.log ε|, hε, by linarith, ?_⟩
  intro δ hδ _
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => η t / (t + δ) := ⟨_, rfl⟩
  have hfv : ∀ t, f t = η t / (t + δ) := fun t => by rw [hf]
  have hfc : ContDiffOn ℝ ∞ f (Set.Ioi (-δ)) := by
    rw [hf]
    refine hηs.contDiffOn.div (contDiffOn_id.add contDiffOn_const) fun t ht => ?_
    have h : 0 < t + δ := by simp only [Set.mem_Ioi] at ht; linarith
    exact h.ne'
  have hfcont := hfc.continuousOn
  have hsub : ∀ a b, -δ < a → -δ < b → Set.uIcc a b ⊆ Set.Ioi (-δ) := fun a b ha hb t ht =>
    lt_of_lt_of_le (lt_inf_iff.2 ⟨ha, hb⟩) ht.1
  have hII : ∀ a b, -δ < a → -δ < b → IntervalIntegrable f volume a b :=
    fun a b ha hb => (hfcont.mono (hsub a b ha hb)).intervalIntegrable
  have hd : ∀ u, -δ < u → HasDerivAt (fun u => ∫ t in ρ0..u, f t) (f u) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_right (hII ρ0 u (by linarith) hu)
      (hfcont.stronglyMeasurableAtFilter isOpen_Ioi u hu)
      (hfcont.continuousAt (isOpen_Ioi.mem_nhds hu))
  have hnn : ∀ t, -δ < t → 0 ≤ f t := fun t ht => by
    rw [hfv]; exact div_nonneg (hηnn t) (by linarith)
  have hzero : ∀ u, ρ0 - ε ≤ u → ∫ t in ρ0..u, f t = 0 := by
    intro u hu
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      have h : ρ0 - ε ≤ t := le_trans (le_inf (by linarith) hu) ht.1
      simp only [hfv, hη0 t h, zero_div]
  have hle0 : ∀ u, 0 ≤ u → ∫ t in ρ0..u, f t ≤ 0 := by
    intro u hu
    rcases le_total u ρ0 with h | h
    · rw [intervalIntegral.integral_symm]
      have := intervalIntegral.integral_nonneg (μ := volume) h fun t ht =>
        hnn t (lt_of_lt_of_le (by linarith) ht.1)
      linarith
    · rw [hzero u (by linarith)]
  refine ⟨fun u => ∫ t in ρ0..u, f t, ?_, hzero, ?_, ?_, ?_⟩
  · exact (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2
      ⟨fun u hu => (hd u hu).differentiableAt.differentiableWithinAt,
       hfc.congr fun u hu => (hd u hu).deriv⟩
  · intro u hu
    have hu' : -δ < u := by linarith
    have hp : 0 < u + δ := by linarith
    have hdg : deriv (fun u => ∫ t in ρ0..u, f t) u = f u := (hd u hu').deriv
    have hηdiff : HasDerivAt η (deriv η u) u := ((hηs.differentiable (by simp)) u).hasDerivAt
    have hfd : HasDerivAt f ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2) u := by
      rw [hf]; exact hηdiff.fun_div ((hasDerivAt_id u).add_const δ) hp.ne'
    have hdd : deriv (deriv (fun u => ∫ t in ρ0..u, f t)) u = deriv f u := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds hu'] with t ht using (hd t ht).deriv
    refine ⟨hle0 u hu, ?_, ?_⟩
    · rw [hdg, hfv]; exact div_nonneg (hηnn u) hp.le
    · rw [hdg, hdd, hfd.deriv, hfv]
      have ha : 0 < 1 / (ρ0 - 4 * ε) := by positivity
      have key : η u / (u + δ) + u * ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2)
          = η u * δ / (u + δ) ^ 2 + u * deriv η u / (u + δ) := by
        field_simp; ring
      rw [key]
      have h1 : 0 ≤ η u * δ / (u + δ) ^ 2 := div_nonneg (mul_nonneg (hηnn u) hδ.le) (sq_nonneg _)
      have h2 : -(1 / (ρ0 - 4 * ε)) ≤ u * deriv η u / (u + δ) := by
        rw [le_div_iff₀ hp]
        nlinarith [mul_le_mul_of_nonneg_left (hηd u) hu, mul_pos ha hδ]
      linarith
  · intro u hu0 huε
    beta_reduce
    have hp : 0 < u + δ := by linarith
    have hεδ : 0 < ε + δ := by linarith
    have hsplit : ∫ t in ρ0..u, f t = (∫ t in ρ0..ε, f t) - ∫ t in u..ε, f t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hII ρ0 ε (by linarith) (by linarith)) (hII ε u (by linarith) (by linarith)),
        intervalIntegral.integral_symm u ε]
      ring
    have hlog : ∫ t in u..ε, f t = Real.log (ε + δ) - Real.log (u + δ) := by
      rw [intervalIntegral.integral_congr (g := fun t => (t + δ)⁻¹) ?_]
      · have h := intervalIntegral.integral_comp_add_right (a := u) (b := ε) (fun t : ℝ => t⁻¹) δ
        rw [h, integral_inv_of_pos hp hεδ, Real.log_div hεδ.ne' hp.ne']
      · intro t ht
        have h : t ≤ ε := le_trans ht.2 (sup_le huε le_rfl)
        simp only [hfv, hη1 t h, one_div]
    rw [hsplit, hlog]
    have h1 := hle0 ε hε.le
    have h2 : Real.log ε ≤ Real.log (ε + δ) := Real.log_le_log hε (by linarith)
    have h3 := neg_abs_le (Real.log ε)
    have h5 : 0 ≤ 2 * ρ0 / ε := by positivity
    linarith
  · intro u hu
    beta_reduce
    have hC : 0 ≤ 2 * ρ0 / ε + |Real.log ε| := by positivity
    rcases le_total u ρ0 with h | h
    · have hu' : -δ < u := by linarith
      rw [intervalIntegral.integral_symm]
      have hb : ∫ t in u..ρ0, f t ≤ ∫ _ in u..ρ0, (2 / ε) := by
        refine intervalIntegral.integral_mono_on h (hII u ρ0 hu' (by linarith))
          intervalIntegrable_const fun t ht => ?_
        have ht1 : ε / 2 ≤ t := le_trans hu ht.1
        have hk : 2 / ε * ε = 2 := div_mul_cancel₀ 2 hε.ne'
        rw [hfv, div_le_iff₀ (by linarith)]
        nlinarith [hηle t, mul_nonneg (div_pos two_pos hε).le (show 0 ≤ t + δ - ε / 2 by linarith)]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hb
      have hm : (ρ0 - u) * (2 / ε) ≤ 2 * ρ0 / ε := by
        rw [show 2 * ρ0 / ε = ρ0 * (2 / ε) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have := abs_nonneg (Real.log ε)
      linarith
    · rw [hzero u (by linarith)]; linarith

end GlobalTheory
