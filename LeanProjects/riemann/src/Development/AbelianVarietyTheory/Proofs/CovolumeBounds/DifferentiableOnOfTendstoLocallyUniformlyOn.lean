import Mathlib

open Metric Set Filter
open scoped Topology ContDiff Nat

namespace GlobalTheory.SCV

section Estimates

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem norm_fderiv_le_of_ball {f : E → V} {c : E} {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f c‖ ≤ 2 * M / r := by
  refine Complex.norm_fderiv_le_div_of_mapsTo_ball hf (fun z hz => ?_) hr
  rw [mem_closedBall_iff_norm]
  have := norm_sub_le (f z) (f c)
  linarith [hM z hz, hM c (mem_ball_self hr)]

theorem norm_sub_sub_fderiv_le_of_ball {f : E → V} {c z : E} {r M : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M)
    (hz : z ∈ ball c r) :
    ‖f z - f c - fderiv ℂ f c (z - c)‖ ≤ 4 * M * (‖z - c‖ / r) ^ 2 := by
  have hr : 0 < r := pos_of_mem_ball hz
  have h1 := norm_fderiv_le_of_ball hr hf hM
  have hc : HasFDerivAt f (fderiv ℂ f c) c :=
    (hf.differentiableAt (ball_mem_nhds c hr)).hasFDerivAt
  set g : E → V := fun w => f w - fderiv ℂ f c (w - c) with hg
  have hgc : g c = f c := by simp [hg]
  have hgw : ∀ w, g w - g c = f w - f c - fderiv ℂ f c (w - c) := by
    intro w; rw [hgc, hg]; simp only; abel
  have key := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (f := g) (c := c) (z := z)
    (R₁ := r) (R₂ := 4 * M) (n := 1) ?_ ?_ ?_ hz
  · rwa [dist_eq_norm, dist_eq_norm, hgw] at key
  · exact hf.sub (by fun_prop)
  · intro w hw
    rw [mem_closedBall_iff_norm, hgw]
    have h2 : ‖fderiv ℂ f c (w - c)‖ ≤ 2 * M := by
      refine ((fderiv ℂ f c).le_opNorm _).trans ?_
      calc _ ≤ (2 * M / r) * r :=
            mul_le_mul h1 (mem_ball_iff_norm.mp hw).le (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = 2 * M := by field_simp
    have := norm_sub_le (f w - f c) (fderiv ℂ f c (w - c))
    have := norm_sub_le (f w) (f c)
    linarith [hM w hw, hM c (mem_ball_self hr)]
  · simp only [hgw, pow_one]
    exact hc.isLittleO.norm_right

theorem tendstoUniformlyOn_fderiv_ball [CompleteSpace V] {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → E → V} {f : E → V} {c : E} {r : ℝ}
    (hlim : TendstoUniformlyOn F f l (ball c (2 * r)))
    (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) (ball c (2 * r))) :
    DifferentiableOn ℂ f (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) l (ball c r) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.mpr hr, differentiableOn_empty, tendstoUniformlyOn_empty]
  have hsub : ∀ x ∈ ball c r, ball x r ⊆ ball c (2 * r) := fun x hx =>
    ball_subset_ball' (by linarith [mem_ball.mp hx])
  have hC : UniformCauchySeqOn (fun n => fderiv ℂ (F n)) l (ball c r) := by
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
    have h1 := hlim.uniformCauchySeqOn _ (Metric.dist_mem_uniformity (ε := ε * r / 4) (by positivity))
    filter_upwards [h1, hF.prod_inl l, hF.prod_inr l] with m hm hm1 hm2 x hx
    apply hεu
    have hn : ball c (2 * r) ∈ 𝓝 x := mem_of_superset (ball_mem_nhds x hr) (hsub x hx)
    rw [dist_eq_norm, ← fderiv_sub (hm1.differentiableAt hn) (hm2.differentiableAt hn)]
    have := norm_fderiv_le_of_ball (f := F m.1 - F m.2) (M := ε * r / 4) hr
      ((hm1.sub hm2).mono (hsub x hx)) (fun z hz => by
        have := hm z (hsub x hx hz)
        simp only [dist_eq_norm] at this
        exact this.le)
    refine this.trans_lt ?_
    rw [div_lt_iff₀ hr]
    nlinarith [mul_pos hε hr]
  set g' : E → E →L[ℂ] V := fun x => limUnder l (fun n => fderiv ℂ (F n) x)
  have hT : TendstoUniformlyOn (fun n => fderiv ℂ (F n)) g' l (ball c r) :=
    hC.tendstoUniformlyOn_of_tendsto fun x hx => (hC.cauchy_map hx).le_nhds_lim
  have hsub' : ball c r ⊆ ball c (2 * r) := ball_subset_ball (by linarith)
  have hD : ∀ x ∈ ball c r, HasFDerivAt f (g' x) x := by
    intro x hx
    have hn : ball c r ∈ 𝓝 x := isOpen_ball.mem_nhds hx
    refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := l) (f := F)
      (f' := fun n => fderiv ℂ (F n)) ?_ ?_ ?_
    · exact (tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mp hT).mono_right
        (le_principal_iff.mpr hn)
    · filter_upwards [hF.prod_inl _, Filter.Eventually.prod_inr hn l] with p hp hp2
      exact (hp.differentiableAt (isOpen_ball.mem_nhds (hsub' hp2))).hasFDerivAt
    · filter_upwards [hn] with y hy using hlim.tendsto_at (hsub' hy)
  exact ⟨fun x hx => (hD x hx).differentiableAt.differentiableWithinAt,
    hT.congr_right fun x hx => (hD x hx).fderiv.symm⟩

theorem exists_ball_bound {f : E → V} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {c : E} (hc : c ∈ U) : ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ z ∈ ball c r, ‖f z‖ ≤ M := by
  have h1 : ContinuousAt f c := (hf.differentiableAt (hU.mem_nhds hc)).continuousAt
  have h2 : ∀ᶠ z in 𝓝 c, z ∈ U ∧ ‖f z‖ < ‖f c‖ + 1 :=
    (Filter.Eventually.and (hU.mem_nhds hc) (h1.norm.eventually (gt_mem_nhds (lt_add_one _))))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp h2
  exact ⟨r, hr, ‖f c‖ + 1, fun z hz => (h z hz).1, fun z hz => (h z hz).2.le⟩

theorem differentiableOn_fderiv_apply [CompleteSpace V] {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun x => fderiv ℂ f x v) U := by
  intro c hc
  obtain ⟨R, hR, M, hRU, hM⟩ := exists_ball_bound hU hf hc
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hR))
  have hsub : ∀ x ∈ ball c (2 * r), ball x (2 * r) ⊆ ball c R := fun x hx =>
    ball_subset_ball' (by linarith [mem_ball.mp hx])
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t • v‖ < 2 * r := by
    have : Tendsto (fun t : ℂ => ‖t • v‖) (𝓝 0) (𝓝 0) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact nhdsWithin_le_nhds (this.eventually (gt_mem_nhds (by positivity)))
  have hmem : ∀ t : ℂ, ‖t • v‖ < 2 * r → ∀ x, x + t • v ∈ ball x (2 * r) := by
    intro t ht x
    simpa [mem_ball_iff_norm] using ht
  have key := tendstoUniformlyOn_fderiv_ball (l := 𝓝[≠] (0 : ℂ))
    (F := fun t x => t⁻¹ • (f (x + t • v) - f x)) (f := fun x => fderiv ℂ f x v) (c := c) (r := r)
    ?_ ?_
  · exact (key.1.differentiableAt (ball_mem_nhds c hr0)).differentiableWithinAt
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h0 : Tendsto (fun t : ℂ => 4 * M * (‖v‖ / (2 * r)) ^ 2 * ‖t‖) (𝓝 0) (𝓝 0) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    filter_upwards [hsmall, nhdsWithin_le_nhds (h0.eventually (gt_mem_nhds hε)),
      self_mem_nhdsWithin] with t ht hte ht0 x hx
    have ht0' : t ≠ 0 := ht0
    have h1 := norm_sub_sub_fderiv_le_of_ball (hf.mono ((hsub x hx).trans hRU))
      (fun z hz => hM z (hsub x hx hz)) (hmem t ht x)
    rw [add_sub_cancel_left, map_smul, norm_smul] at h1
    have h2 : t⁻¹ • (f (x + t • v) - f x) - fderiv ℂ f x v
        = t⁻¹ • (f (x + t • v) - f x - t • fderiv ℂ f x v) := by
      rw [smul_sub t⁻¹ (_ - _), inv_smul_smul₀ ht0']
    rw [dist_comm, dist_eq_norm, h2, norm_smul, norm_inv]
    have htp : 0 < ‖t‖ := norm_pos_iff.mpr ht0'
    refine lt_of_le_of_lt ?_ hte
    rw [inv_mul_le_iff₀ htp]
    refine h1.trans_eq ?_
    ring
  · filter_upwards [hsmall] with t ht
    refine DifferentiableOn.const_smul (DifferentiableOn.sub ?_ ?_) _
    · exact hf.comp (by fun_prop) fun x hx => hRU (hsub x hx (hmem t ht x))
    · exact hf.mono ((ball_subset_ball (by linarith)).trans hRU)

end Estimates

section FiniteDimensional

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem contDiffOn_nat {U : Set E} (hU : IsOpen U) (n : ℕ) :
    ∀ {f : E → V}, DifferentiableOn ℂ f U → ContDiffOn ℂ n f U := by
  induction n with
  | zero =>
    intro f hf
    simpa using hf.continuousOn
  | succ n ih =>
    intro f hf
    rw [Nat.cast_succ]
    refine contDiffOn_succ_of_fderiv_apply hf (by simp) fun y => ?_
    refine (ih (differentiableOn_fderiv_apply hU hf y)).congr fun x hx => ?_
    rw [fderivWithin_of_isOpen hU hx]

theorem differentiableOn_iteratedFDeriv {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) : DifferentiableOn ℂ (iteratedFDeriv ℂ n f) U :=
  fun _ hx => (((contDiffOn_nat hU (n + 1) hf).contDiffAt
    (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self n)).differentiableWithinAt

theorem norm_iteratedFDeriv_le_pow {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {δ M : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∀ x : E, closedBall x (n * δ) ⊆ U → (∀ z ∈ closedBall x (n * δ), ‖f z‖ ≤ M) →
      ‖iteratedFDeriv ℂ n f x‖ ≤ M * (2 / δ) ^ n := by
  induction n with
  | zero =>
    intro x _ hM
    simpa using hM x (by simp)
  | succ n ih =>
    intro x hx hM
    have hsub : ∀ y ∈ ball x δ, closedBall y (n * δ) ⊆ closedBall x ((n + 1 : ℕ) * δ) :=
      fun y hy => closedBall_subset_closedBall' (by
        push_cast
        linarith [mem_ball.mp hy])
    have hball : ball x δ ⊆ U := fun y hy =>
      hx (hsub y hy (mem_closedBall_self (by positivity)))
    rw [← norm_fderiv_iteratedFDeriv]
    refine (norm_fderiv_le_of_ball (M := M * (2 / δ) ^ n) hδ
      ((differentiableOn_iteratedFDeriv hU hf n).mono hball)
      fun y hy => ih y ((hsub y hy).trans hx) fun z hz => hM z (hsub y hy hz)).trans_eq ?_
    ring

theorem norm_iteratedFDeriv_le_factorial {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} {R M : ℝ} (hR : 0 < R) (hc : closedBall c R ⊆ U)
    (hM : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖iteratedFDeriv ℂ n f c‖ ≤ n ! * (M * (2 * Real.exp 1 / R) ^ n) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_closedBall_self hR.le))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hM c (mem_closedBall_self hR.le)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℝ) * (R / n) = R := by field_simp
  have h1 := norm_iteratedFDeriv_le_pow hU hf (δ := R / n) (M := M) (by positivity) n c
    (by rwa [e]) (by rwa [e])
  have h2 := Real.pow_div_factorial_le_exp (n : ℝ) hn'.le n
  rw [div_le_iff₀ (by positivity), ← Real.exp_one_pow] at h2
  refine h1.trans ?_
  calc M * (2 / (R / n)) ^ n = (M * (2 / R) ^ n) * (n : ℝ) ^ n := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        field_simp
    _ ≤ (M * (2 / R) ^ n) * (Real.exp 1 ^ n * n !) := by gcongr
    _ = n ! * (M * (2 * Real.exp 1 / R) ^ n) := by
        rw [show 2 * Real.exp 1 / R = 2 / R * Real.exp 1 by ring, mul_pow]
        ring

theorem iteratedDeriv_line {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} (hc : c ∈ U) (y : E) (n : ℕ) :
    iteratedDeriv n (fun t : ℂ => f (c + t • y)) 0 = iteratedFDeriv ℂ n f c (fun _ => y) := by
  set L : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ y with hL
  set s : Set E := (fun w => c + w) ⁻¹' U with hs
  have hso : IsOpen s := hU.preimage (by fun_prop)
  have hso' : IsOpen (L ⁻¹' s) := hso.preimage L.continuous
  have hg : DifferentiableOn ℂ (fun w => f (c + w)) s :=
    hf.comp (by fun_prop) fun w hw => hw
  have h0 : L 0 ∈ s := by simpa [hs] using hc
  have key := L.iteratedFDerivWithin_comp_right (contDiffOn_nat hso n hg) hso.uniqueDiffOn
    hso'.uniqueDiffOn h0 le_rfl
  rw [iteratedFDerivWithin_of_isOpen n hso' (show (0 : ℂ) ∈ L ⁻¹' s from h0),
    iteratedFDerivWithin_of_isOpen n hso h0, iteratedFDeriv_comp_add_left] at key
  have e : (fun t : ℂ => f (c + t • y)) = (fun w => f (c + w)) ∘ L := by
    ext t
    simp [hL]
  rw [iteratedDeriv_eq_iteratedFDeriv, e, key]
  simp [hL]

theorem hasSum_taylorSeries_ball {f : E → V} {c : E} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) {y : E} (hy : ‖y‖ < R) :
    HasSum (fun n : ℕ => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c (fun _ => y)) (f (c + y)) := by
  have hy0 := norm_nonneg y
  have hR : 0 < R := hy0.trans_lt hy
  have hp : 0 < R + ‖y‖ := by linarith
  have hg : DifferentiableOn ℂ (fun t : ℂ => f (c + t • y)) (ball 0 (2 * R / (R + ‖y‖))) := by
    refine hf.comp (by fun_prop) fun t ht => ?_
    rw [mem_ball_zero_iff, lt_div_iff₀ hp] at ht
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
    have := norm_nonneg t
    nlinarith [mul_nonneg this (sub_nonneg.mpr hy.le)]
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (2 * R / (R + ‖y‖)) := by
    rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hp]
    linarith
  have key := Complex.hasSum_taylorSeries_on_ball hg h1
  simpa only [iteratedDeriv_line isOpen_ball hf (mem_ball_self hR), sub_zero, one_pow, one_smul]
    using key

theorem hasFPowerSeriesAt_taylor {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c : E} (hc : c ∈ U) :
    HasFPowerSeriesAt f (fun n => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c) c := by
  obtain ⟨R, hR, M, hRU, hM⟩ := exists_ball_bound hU hf hc
  have hsub : closedBall c (R / 2) ⊆ ball c R := closedBall_subset_ball (by linarith)
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hρ : 0 < R / 2 / (2 * Real.exp 1) := by positivity
  let ρ : NNReal := ⟨R / 2 / (2 * Real.exp 1), hρ.le⟩
  have hρe : (ρ : ℝ) = R / 2 / (2 * Real.exp 1) := rfl
  refine ⟨ρ, ?_, ?_, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ M fun n => ?_
    have h1 := norm_iteratedFDeriv_le_factorial hU hf (half_pos hR) (hsub.trans hRU)
      (fun z hz => hM z (hsub hz)) n
    have hn : (0 : ℝ) < n ! := by positivity
    have h2 : ‖(n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c‖ ≤ M * (2 * Real.exp 1 / (R / 2)) ^ n := by
      rw [norm_smul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hn]
      exact h1
    calc ‖(n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c‖ * (ρ : ℝ) ^ n
        ≤ (M * (2 * Real.exp 1 / (R / 2)) ^ n) * (ρ : ℝ) ^ n := by gcongr
      _ = M := by
        rw [mul_assoc, ← mul_pow, hρe,
          show 2 * Real.exp 1 / (R / 2) * (R / 2 / (2 * Real.exp 1)) = 1 by field_simp]
        simp
  · exact_mod_cast hρ
  · intro y hy
    rw [Metric.eball_coe, mem_ball_zero_iff, hρe, lt_div_iff₀ (by positivity)] at hy
    have hy' : ‖y‖ < R := by nlinarith [norm_nonneg y]
    simpa only [smul_apply]
      using hasSum_taylorSeries_ball (hf.mono hRU) hy'

theorem analyticOnNhd_of_differentiableOn {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U :=
  fun _ hc => (hasFPowerSeriesAt_taylor hU hf hc).analyticAt

theorem analyticOnNhd_iff_differentiableOn {f : E → V} {U : Set E} (hU : IsOpen U) :
    AnalyticOnNhd ℂ f U ↔ DifferentiableOn ℂ f U :=
  ⟨AnalyticOnNhd.differentiableOn, analyticOnNhd_of_differentiableOn hU⟩

theorem analyticAt_of_differentiableOn {f : E → V} {s : Set E} {c : E}
    (hf : DifferentiableOn ℂ f s) (hs : s ∈ 𝓝 c) : AnalyticAt ℂ f c :=
  analyticOnNhd_of_differentiableOn isOpen_interior (hf.mono interior_subset) c
    (mem_interior_iff_mem_nhds.mpr hs)

theorem analyticAt_iff_eventually_differentiableAt {f : E → V} {c : E} :
    AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z :=
  ⟨fun h => h.eventually_analyticAt.mono fun _ hz => hz.differentiableAt,
    fun h => analyticAt_of_differentiableOn (s := {z | DifferentiableAt ℂ f z})
      (fun _ hz => DifferentiableAt.differentiableWithinAt hz) h⟩

theorem analyticOnNhd_of_differentiable {f : E → V} (hf : Differentiable ℂ f) (s : Set E) :
    AnalyticOnNhd ℂ f s :=
  fun c _ => analyticOnNhd_of_differentiableOn isOpen_univ hf.differentiableOn c (mem_univ c)

theorem contDiffOn_of_differentiableOn {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (n : WithTop ℕ∞) : ContDiffOn ℂ n f U :=
  (analyticOnNhd_of_differentiableOn hU hf).contDiffOn_of_completeSpace

theorem contDiffAt_of_differentiableOn {f : E → V} {s : Set E} {c : E}
    (hf : DifferentiableOn ℂ f s) (hs : s ∈ 𝓝 c) (n : WithTop ℕ∞) : ContDiffAt ℂ n f c :=
  (analyticAt_of_differentiableOn hf hs).contDiffAt

theorem contDiff_of_differentiable {f : E → V} (hf : Differentiable ℂ f) (n : WithTop ℕ∞) :
    ContDiff ℂ n f :=
  (analyticOnNhd_of_differentiable hf univ).contDiff

theorem differentiableOn_fderiv {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : DifferentiableOn ℂ (fderiv ℂ f) U :=
  (analyticOnNhd_of_differentiableOn hU hf).fderiv.differentiableOn

theorem eqOn_of_eventuallyEq {f g : E → V} {U : Set E} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {c : E} (hc : c ∈ U)
    (hfg : f =ᶠ[𝓝 c] g) : EqOn f g U :=
  (analyticOnNhd_of_differentiableOn hU hf).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_of_differentiableOn hU hg) hU' hc hfg

theorem eqOn_of_eqOn_open {f g : E → V} {U W : Set E} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hW : IsOpen W)
    (hne : W.Nonempty) (hWU : W ⊆ U) (hfg : EqOn f g W) : EqOn f g U := by
  obtain ⟨c, hc⟩ := hne
  exact eqOn_of_eventuallyEq hU hU' hf hg (hWU hc)
    (hfg.eventuallyEq_of_mem (hW.mem_nhds hc))

section Limits

variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}

private theorem exists_ball_limit [l.NeBot] (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    {c : E} (hc : c ∈ U) : ∃ r > 0, DifferentiableOn ℂ f (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) l (ball c r) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU c hc
  have hsub : closedBall c (2 * (R / 4)) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  have h1 := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _ hsub
    (isCompact_closedBall _ _)
  exact ⟨R / 4, by positivity, tendstoUniformlyOn_fderiv_ball (h1.mono ball_subset_closedBall)
    (hF.mono fun n hn => hn.mono (ball_subset_closedBall.trans hsub))⟩

theorem differentiableOn_of_tendstoLocallyUniformlyOn [l.NeBot] (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) :
    DifferentiableOn ℂ f U := by
  intro c hc
  obtain ⟨r, hr, h, -⟩ := exists_ball_limit hU hlim hF hc
  exact (h.differentiableAt (ball_mem_nhds c hr)).differentiableWithinAt

theorem tendstoLocallyUniformlyOn_fderiv (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) :
    TendstoLocallyUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) l U := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun c hc => ?_
  rcases l.eq_or_neBot with rfl | hne
  · exact ⟨U, self_mem_nhdsWithin, by simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]⟩
  obtain ⟨r, hr, -, h⟩ := exists_ball_limit hU hlim hF hc
  exact ⟨ball c r, nhdsWithin_le_nhds (ball_mem_nhds c hr), h⟩

theorem tendstoLocallyUniformlyOn_iteratedFDeriv (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    (k : ℕ) :
    TendstoLocallyUniformlyOn (fun n => iteratedFDeriv ℂ k (F n)) (iteratedFDeriv ℂ k f) l U := by
  induction k with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℂ E V).symm.isometry.uniformContinuous
      |>.comp_tendstoLocallyUniformlyOn hlim
  | succ k ih =>
    simp only [iteratedFDeriv_succ_eq_comp_left]
    exact (continuousMultilinearCurryLeftEquiv ℂ (fun _ : Fin (k + 1) => E)
      V).symm.isometry.uniformContinuous.comp_tendstoLocallyUniformlyOn
      (tendstoLocallyUniformlyOn_fderiv hU ih
        (hF.mono fun n hn => differentiableOn_iteratedFDeriv hU hn k))

theorem differentiableOn_of_hasSumLocallyUniformlyOn (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn F f U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    DifferentiableOn ℂ f U :=
  differentiableOn_of_tendstoLocallyUniformlyOn hU
    (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hsum)
    (Eventually.of_forall fun _ => DifferentiableOn.fun_sum fun i _ => hF i)

theorem hasSumLocallyUniformlyOn_fderiv (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn F f U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) :
    HasSumLocallyUniformlyOn (fun i => fderiv ℂ (F i)) (fderiv ℂ f) U := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hsum ⊢
  refine (tendstoLocallyUniformlyOn_fderiv hU hsum
    (Eventually.of_forall fun _ => DifferentiableOn.fun_sum fun i _ => hF i)).congr
    fun s z hz => ?_
  exact fderiv_fun_sum fun i _ => (hF i).differentiableAt (hU.mem_nhds hz)

theorem hasSumLocallyUniformlyOn_iteratedFDeriv (hU : IsOpen U)
    (hsum : HasSumLocallyUniformlyOn F f U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (k : ℕ) :
    HasSumLocallyUniformlyOn (fun i => iteratedFDeriv ℂ k (F i)) (iteratedFDeriv ℂ k f) U := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hsum ⊢
  refine (tendstoLocallyUniformlyOn_iteratedFDeriv hU hsum
    (Eventually.of_forall fun _ => DifferentiableOn.fun_sum fun i _ => hF i) k).congr
    fun s z hz => ?_
  exact iteratedFDeriv_fun_sum_apply fun i _ =>
    contDiffAt_of_differentiableOn (hF i) (hU.mem_nhds hz) _

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedSpace ℂ V] in

theorem hasSumLocallyUniformlyOn_of_locally_normal
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i) :
    HasSumLocallyUniformlyOn F (fun z => ∑' i, F i z) U := by
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun x hx => ?_
  obtain ⟨t, ht, u, hu, h⟩ := hle x hx
  exact ⟨t, nhdsWithin_le_nhds ht, tendstoUniformlyOn_tsum hu h⟩

theorem differentiableOn_tsum_of_locally_normal (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∑' i, F i z) U :=
  differentiableOn_of_hasSumLocallyUniformlyOn hU
    (hasSumLocallyUniformlyOn_of_locally_normal hle) hF

theorem hasSum_fderiv_of_locally_normal (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i)
    {z : E} (hz : z ∈ U) :
    HasSum (fun i => fderiv ℂ (F i) z) (fderiv ℂ (fun w => ∑' i, F i w) z) :=
  (hasSumLocallyUniformlyOn_fderiv hU (hasSumLocallyUniformlyOn_of_locally_normal hle) hF).hasSum hz

theorem hasSum_iteratedFDeriv_of_locally_normal (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i)
    (k : ℕ) {z : E} (hz : z ∈ U) :
    HasSum (fun i => iteratedFDeriv ℂ k (F i) z) (iteratedFDeriv ℂ k (fun w => ∑' i, F i w) z) :=
  (hasSumLocallyUniformlyOn_iteratedFDeriv hU (hasSumLocallyUniformlyOn_of_locally_normal hle)
    hF k).hasSum hz

theorem differentiableOn_tsum_of_normal_on_compacts (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ K, ‖F i z‖ ≤ u i) :
    DifferentiableOn ℂ (fun z => ∑' i, F i z) U ∧
      ∀ k : ℕ, HasSumLocallyUniformlyOn (fun i => iteratedFDeriv ℂ k (F i))
        (iteratedFDeriv ℂ k (fun w => ∑' i, F i w)) U := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i := by
    intro x hx
    obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
    exact ⟨K, hKx, hle K hKU hK⟩
  exact ⟨differentiableOn_tsum_of_locally_normal hU hF h, fun k =>
    hasSumLocallyUniformlyOn_iteratedFDeriv hU
      (hasSumLocallyUniformlyOn_of_locally_normal h) hF k⟩

end Limits

end FiniteDimensional

end GlobalTheory.SCV
