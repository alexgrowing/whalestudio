import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ResidueVanishing.Leaves

noncomputable section

open Filter Topology Set Metric GlobalTheory.Cont

namespace PositivityTheory.Rg.Rsw.Kplug

theorem k2b2_tendsto {s₀ : ℂ} : ∀ (k : ℕ) {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}, HasFPowerSeriesAt g p s₀ →
    (∀ i < k, p.coeff i = 0) → Tendsto (fun s => g s / (s - s₀) ^ k) (𝓝[≠] s₀) (𝓝 (p.coeff k)) := by
  intro k g p hp hk
  have hG := hp.has_fpower_series_iterate_dslope_fslope k
  have hval : ∀ j, (Function.swap dslope s₀)^[j] g s₀ = p.coeff j := fun j => by
    rw [← (hp.has_fpower_series_iterate_dslope_fslope j).coeff_zero 1]
    have := FormalMultilinearSeries.coeff_iterate_fslope (p := p) j 0
    rw [zero_add] at this
    exact this
  have hz : ∀ j < k, (Function.swap dslope s₀)^[j] g s₀ = 0 := fun j hj => by
    rw [hval j, hk j hj]
  have heq := pow_sub_smul_iterate_dslope_of_zero k hz
  have hc : Tendsto ((Function.swap dslope s₀)^[k] g) (𝓝[≠] s₀) (𝓝 (p.coeff k)) := by
    rw [← hval k]
    exact hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
  rw [← heq s, smul_eq_mul, mul_div_cancel_left₀ _ hne]

theorem k2b2_cps (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (n : ℕ) :
    (cauchyPowerSeries f c R).coeff n =
      (2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(c, R), (1 / (z - c)) ^ n • (z - c)⁻¹ • f z :=
  cauchyPowerSeries_apply f c R n 1

theorem continuation_pole_order : PositivityTheory.Rg.Rsw.Kplug.K2 := by
  intro h e U d s₀ ε σ hU hRD he hd hrad hED hres
  obtain ⟨hε, hball, hdne⟩ := hrad
  set c : ℂ := (2 * ↑Real.pi * Complex.I)⁻¹ *
    ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (1 - 1) * (e z / Polynomial.eval z d) with hc
  set H : ℂ → ℂ := fun z => e z / Polynomial.eval z d with hH
  have hs₀U : s₀ ∈ U := hball (mem_closedBall_self hε.le)
  have hdan : ∀ z, AnalyticAt ℂ (fun z => Polynomial.eval z d) z := fun z =>
    Differentiable.analyticAt (Polynomial.differentiable d) z
  have hean : AnalyticOnNhd ℂ e U := he.analyticOnNhd hU
  have hHmer : ∀ z ∈ U, MeromorphicAt H z := fun z hz =>
    (hean z hz).meromorphicAt.div (hdan z).meromorphicAt
  have hext : IsExtAt h s₀ H := by
    refine ⟨U, hs₀U, hRD, hHmer, ?_⟩
    obtain ⟨M, hM⟩ := ((Polynomial.finite_setOf_isRoot hd).image Complex.re).bddAbove
    refine ⟨max σ M, fun z hz => ?_⟩
    have hz' : max σ M < z.re := hz
    have hdz : Polynomial.eval z d ≠ 0 := by
      intro h0
      have : z.re ≤ M := hM ⟨z, h0, rfl⟩
      exact absurd hz' (not_lt.mpr (le_max_of_le_right this))
    simp only [hH, hED z (lt_of_le_of_lt (le_max_left _ _) hz')]
    field_simp
  have hT : Tendsto (fun s => (s - s₀) * H s) (𝓝[≠] s₀) (𝓝 c) := by
    obtain ⟨q, hdq, hndvd⟩ := d.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hd s₀
    generalize hm : Polynomial.rootMultiplicity s₀ d = m at hdq
    have hq0 : q.eval s₀ ≠ 0 := fun h0 => hndvd (Polynomial.dvd_iff_isRoot.mpr h0)
    have hdeval : ∀ z, Polynomial.eval z d = (z - s₀) ^ m * q.eval z := fun z => by
      have := congrArg (Polynomial.eval z) hdq
      simpa using this
    have hqne : ∀ z ∈ closedBall s₀ ε, q.eval z ≠ 0 := by
      intro z hz h0
      by_cases hzs : z = s₀
      · exact hq0 (hzs ▸ h0)
      · exact hdne z hz hzs (by rw [hdeval, h0, mul_zero])
    set F : ℂ → ℂ := fun z => e z / q.eval z with hF
    have hFd : DifferentiableOn ℂ F (closedBall s₀ ε) :=
      (he.mono hball).div q.differentiable.differentiableOn hqne
    set R : NNReal := ε.toNNReal with hRdef
    have hR : (R : ℝ) = ε := Real.coe_toNNReal _ hε.le
    have hRpos : 0 < R := Real.toNNReal_pos.mpr hε
    have hFps := (show DifferentiableOn ℂ F (closedBall s₀ (R : ℝ)) by rw [hR]; exact hFd).hasFPowerSeriesOnBall hRpos
    have hcf : ∀ j, j + 1 ≤ m → (cauchyPowerSeries F s₀ (R : ℝ)).coeff j =
        (2 * ↑Real.pi * Complex.I)⁻¹ *
          ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (m - 1 - j) * (e z / Polynomial.eval z d) := by
      intro j hj
      rw [k2b2_cps, hR, smul_eq_mul]
      congr 1
      apply circleIntegral.integral_congr hε.le
      intro z hz
      have hzs : z - s₀ ≠ 0 := sub_ne_zero.mpr (ne_of_mem_sphere hz hε.ne')
      obtain ⟨r, hr⟩ : ∃ r, m = r + j + 1 := ⟨m - 1 - j, by omega⟩
      have hr' : m - 1 - j = r := by omega
      simp only [smul_eq_mul, hdeval, hF, hr', hr]
      by_cases hqz : q.eval z = 0
      · simp [hqz]
      · generalize z - s₀ = w at hzs ⊢
        generalize e z = a
        generalize Polynomial.eval z q = b at hqz ⊢
        rw [show r + j + 1 - 1 - j = r by omega, pow_succ, pow_add, one_div, inv_pow]
        field_simp
    have hFan := hFps.hasFPowerSeriesAt
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have hc0 : c = 0 := by
        have hI : ∮ (z : ℂ) in C(s₀, ε), (z - s₀) ^ (1 - 1) * (e z / Polynomial.eval z d) =
            ∮ (z : ℂ) in C(s₀, ε), F z := by
          apply circleIntegral.integral_congr hε.le
          intro z hz
          simp [hdeval, hm0, hF]
        rw [hc, hI, Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le
          Set.countable_empty hFd.continuousOn, mul_zero]
        intro z hz
        exact hFd.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hz.1) ball_subset_closedBall)
      rw [hc0]
      have hlim : Tendsto (fun s => (s - s₀) * F s) (𝓝 s₀) (𝓝 ((s₀ - s₀) * F s₀)) :=
        ((continuous_id.sub continuous_const).continuousAt.mul hFan.continuousAt).tendsto
      rw [sub_self, zero_mul] at hlim
      refine (hlim.mono_left nhdsWithin_le_nhds).congr' (Filter.Eventually.of_forall fun s => ?_)
      simp [hH, hF, hdeval, hm0]
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
      have hcoef : ∀ i < n, (cauchyPowerSeries F s₀ (R : ℝ)).coeff i = 0 := by
        intro i hi
        rw [hcf i (by omega)]
        have := hres (n + 1 - i) (by omega)
        rwa [show n + 1 - i - 1 = n + 1 - 1 - i by omega] at this
      have hlim := k2b2_tendsto n hFan hcoef
      rw [hcf n (by omega), show n + 1 - 1 - n = 1 - 1 by omega] at hlim
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hw : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
      simp only [hH, hF, hdeval]
      by_cases hqs : Polynomial.eval s q = 0
      · simp [hqs]
      · rw [pow_succ]
        field_simp
  refine ⟨⟨H, hext, 0, by simp, ?_⟩, ⟨H, hext, ?_⟩⟩
  · refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp
  · have hmer : MeromorphicAt ((fun s => s - s₀) * H) s₀ :=
      (by fun_prop : MeromorphicAt (fun s => s - s₀) s₀).mul (hHmer s₀ hs₀U)
    have h0 : 0 ≤ meromorphicOrderAt ((fun s => s - s₀) * H) s₀ :=
      (tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer).mp ⟨c, hT⟩
    rw [meromorphicOrderAt_mul (by fun_prop) (hHmer s₀ hs₀U), meromorphicOrderAt_id_sub_const] at h0
    cases ho : meromorphicOrderAt H s₀ with
    | top => exact le_top
    | coe n =>
      rw [ho] at h0
      have : (0 : WithTop ℤ) ≤ ((1 + n : ℤ) : WithTop ℤ) := by exact_mod_cast h0
      have h1 : (0 : ℤ) ≤ 1 + n := by exact_mod_cast this
      exact_mod_cast (by omega : (-(1 : ℕ) : ℤ) ≤ n)

end PositivityTheory.Rg.Rsw.Kplug

end
