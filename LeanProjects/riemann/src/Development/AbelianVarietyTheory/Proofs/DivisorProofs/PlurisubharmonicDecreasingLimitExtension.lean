import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

open ReciprocityTheory.L2DbarEstimates MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff Topology

namespace GlobalTheory.HormanderLimit

theorem exists_tendstoLocallyUniformlyOn_ultrafilter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {F : ℕ → E → ℂ} (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ c ∈ U, ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ k, ∀ z ∈ ball c r, ‖F k z‖ ≤ M)
    (𝒰 : Ultrafilter ℕ) : ∃ f : E → ℂ, TendstoLocallyUniformlyOn F f (𝒰 : Filter ℕ) U := by
  have hpt : ∀ c, ∃ a : ℂ, c ∈ U → Tendsto (fun k => F k c) (𝒰 : Filter ℕ) (𝓝 a) := by
    intro c
    by_cases hc : c ∈ U
    · obtain ⟨r, hr, M, -, hM⟩ := hb c hc
      obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : ℂ) M).ultrafilter_le_nhds
        (𝒰.map fun k => F k c) (by
          rw [le_principal_iff, Ultrafilter.coe_map, mem_map]
          exact Eventually.of_forall fun k => by
            simpa using hM k c (mem_ball_self hr))
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose f hf using hpt
  refine ⟨f, Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε c hc => ?_⟩
  obtain ⟨r, hr, M, hrU, hM⟩ := hb c hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 c (mem_ball_self hr))
  set L : ℝ := (2 * M + 1) / r with hL
  have hL0 : 0 < L := by positivity
  have hlip : ∀ k, ∀ z ∈ ball c r, dist (F k z) (F k c) ≤ L * dist z c := by
    intro k z hz
    refine Complex.dist_le_div_mul_dist_of_mapsTo_ball ((hF k).mono hrU) (fun w hw => ?_) hz
    have := norm_sub_le (F k w) (F k c)
    have h2 : dist (F k w) (F k c) < 2 * M + 1 := by
      rw [dist_eq_norm]
      linarith [hM k w hw, hM k c (mem_ball_self hr)]
    first
      | exact mem_ball.2 h2
      | exact mem_closedBall.2 h2.le
  have hlipf : ∀ z ∈ ball c r, dist (f z) (f c) ≤ L * dist z c := fun z hz =>
    le_of_tendsto ((hf z (hrU hz)).dist (hf c hc)) (Eventually.of_forall fun k => hlip k z hz)
  refine ⟨ball c (min r (ε / (3 * L))), nhdsWithin_le_nhds (ball_mem_nhds c (by positivity)), ?_⟩
  filter_upwards [(Metric.tendsto_nhds.1 (hf c hc)) (ε / 3) (by positivity)] with k hk y hy
  have hy1 : y ∈ ball c r := ball_subset_ball (min_le_left _ _) hy
  have hy2 : dist y c < ε / (3 * L) := (mem_ball.1 hy).trans_le (min_le_right _ _)
  have hy3 : L * dist y c < ε / 3 := by
    rw [lt_div_iff₀ (by positivity)] at hy2
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have h1 := hlipf y hy1
  have h2 := hlip k y hy1
  have h3 := dist_triangle4 (f y) (f c) (F k c) (F k y)
  rw [dist_comm (F k y)] at h2
  rw [dist_comm] at hk
  linarith

theorem enorm_sq_le_lintegral {n : ℕ} {g : V n → ℂ} {c : V n} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) :
    ‖g c‖ₑ ^ 2 ≤ (volume (closedBall (0 : V n) r))⁻¹ * ∫⁻ z in closedBall c r, ‖g z‖ₑ ^ 2 := by
  have hd : DifferentiableOn ℂ (fun z => g (c + z)) (ball 0 r) :=
    hg.comp (by fun_prop) fun z hz => by simpa [mem_ball_iff_norm] using hz
  obtain ⟨-, h1, -⟩ := GlobalTheory.submean_sq_closedBall hr hd
  have h2 := (measurePreserving_add_left (volume : Measure (V n)) c).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft c).measurableEmbedding (fun z => ‖g z‖ₑ ^ 2) (closedBall c r)
  have h3 : (fun z => c + z) ⁻¹' closedBall c r = closedBall 0 r := by
    ext z
    simp [mem_closedBall_iff_norm]
  rw [h3] at h2
  rw [← h2]
  simpa using h1

theorem locally_bounded_of_lintegral {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {F : ℕ → V n → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z in K, ‖F k z‖ₑ ^ 2 ≤ C) :
    ∀ c ∈ U, ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ k, ∀ z ∈ ball c r, ‖F k z‖ ≤ M := by
  intro c hc
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU c hc
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall c (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  obtain ⟨C, hC, hCk⟩ := hb _ hK (isCompact_closedBall _ _)
  set B : ℝ≥0∞ := (volume (closedBall (0 : V n) r))⁻¹ * C with hB
  have hBt : B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (measure_closedBall_pos _ _ hr0).ne') hC
  refine ⟨r, hr0, Real.sqrt B.toReal, (ball_subset_ball (by linarith)).trans hRU,
    fun k z hz => ?_⟩
  have hsub : closedBall z r ⊆ closedBall c (2 * r) :=
    closedBall_subset_closedBall' (by linarith [mem_ball.1 hz])
  have h1 := enorm_sq_le_lintegral hr0
    ((hF k).mono (ball_subset_closedBall.trans (hsub.trans hK)))
  have h2 : ‖F k z‖ₑ ^ 2 ≤ B :=
    h1.trans (by
      rw [hB]
      gcongr
      exact (lintegral_mono_set hsub).trans (hCk k))
  refine Real.le_sqrt_of_sq_le ?_
  have h3 := ENNReal.toReal_mono hBt h2
  simpa using h3

theorem exists_limit {n : ℕ} {U : Set (V n)} (hU : IsOpen U) (K : ℕ → Set (V n))
    (hKc : ∀ j, IsCompact (K j)) (hKU : ∀ j, K j ⊆ U) (hK : ∀ y ∈ U, ∀ᶠ j in atTop, y ∈ K j)
    {φ : ℕ → V n → ℝ} (hφ : ∀ k, ContinuousOn (φ k) U) (hdec : ∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y)
    {F0 : V n → ℂ} (hF0 : ContinuousOn F0 U) {A : ℝ≥0∞} (hA : A ≠ ⊤) {F : ℕ → V n → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hest : ∀ k, ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F k y‖ ^ 2 * Real.exp (-φ k y)) ≤ A) :
    ∃ f : V n → ℂ, DifferentiableOn ℂ f U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  have hanti : ∀ y ∈ U, Antitone fun k => φ k y := fun y hy =>
    antitone_nat_of_succ_le fun k => hdec k y hy
  have hloc : ∀ S ⊆ U, IsCompact S → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z in S, ‖F k z‖ₑ ^ 2 ≤ C := by
    intro S hSU hS
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn ((hφ 0).mono hSU)
    obtain ⟨N, hN⟩ := hS.exists_bound_of_continuousOn (hF0.mono hSU)
    refine ⟨ENNReal.ofReal (2 * N ^ 2) * volume S + ENNReal.ofReal (2 * Real.exp M) * A,
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA⟩, fun k => ?_⟩
    calc ∫⁻ z in S, ‖F k z‖ₑ ^ 2
        ≤ ∫⁻ z in S, (ENNReal.ofReal (2 * N ^ 2) + ENNReal.ofReal (2 * Real.exp M) *
            ENNReal.ofReal (‖F0 z - F k z‖ ^ 2 * Real.exp (-φ k z))) := by
          refine setLIntegral_mono' hS.measurableSet fun z hz => ?_
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : φ k z ≤ M :=
            (hanti z (hSU hz) (Nat.zero_le k)).trans ((le_abs_self _).trans (hM z hz))
          have h2 : 1 ≤ Real.exp M * Real.exp (-φ k z) := by
            rw [← Real.exp_add]
            exact Real.one_le_exp (by linarith)
          have h3 : ‖F k z‖ ≤ N + ‖F0 z - F k z‖ := by
            have := norm_sub_le (F0 z) (F0 z - F k z)
            rw [sub_sub_cancel] at this
            linarith [hN z hz]
          have h4 : ‖F k z‖ ^ 2 ≤ (N + ‖F0 z - F k z‖) ^ 2 := by gcongr
          have h5 : ‖F0 z - F k z‖ ^ 2 * 1 ≤
              ‖F0 z - F k z‖ ^ 2 * (Real.exp M * Real.exp (-φ k z)) := by gcongr
          nlinarith [sq_nonneg (N - ‖F0 z - F k z‖)]
      _ ≤ _ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact (lintegral_mono_set hSU).trans (hest k)
  obtain ⟨f, hf⟩ := exists_tendstoLocallyUniformlyOn_ultrafilter hF
    (locally_bounded_of_lintegral hU hF hloc) (hyperfilter ℕ)
  have hfd : DifferentiableOn ℂ f U :=
    GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hU hf (Eventually.of_forall hF)
  have hsel : ∀ j : ℕ, ∃ k, j ≤ k ∧ ∀ y ∈ K j, dist (f y) (F k y) < 1 / ((j : ℝ) + 1) := by
    intro j
    have h1 := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hf (K j) (hKU j) (hKc j))
      (1 / ((j : ℝ) + 1)) (by positivity)
    have h2 : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), j ≤ k :=
      Nat.hyperfilter_le_atTop (eventually_ge_atTop j)
    exact (h2.and h1).exists
  choose σ hσ hσK using hsel
  have hlim : ∀ y ∈ U, Tendsto (fun j => F (σ j) y) atTop (𝓝 (f y)) := by
    intro y hy
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hK y hy] with j hj
    rw [dist_comm]
    exact (hσK j y hj).le
  have hmeas : ∀ {g : V n → ℂ}, ContinuousOn g U → ∀ m, AEMeasurable
      (fun y => ENNReal.ofReal (‖F0 y - g y‖ ^ 2 * Real.exp (-φ m y))) (volume.restrict U) := by
    intro g hg m
    exact (ContinuousOn.aemeasurable ((((hF0.sub hg).norm).pow 2).mul (hφ m).neg.rexp)
      hU.measurableSet).ennreal_ofReal
  have hm : ∀ m, ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ m y)) ≤ A := by
    intro m
    calc ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ m y))
        = ∫⁻ y in U, liminf (fun j =>
            ENNReal.ofReal (‖F0 y - F (σ j) y‖ ^ 2 * Real.exp (-φ m y))) atTop := by
          refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
          refine (Tendsto.liminf_eq ?_).symm
          exact ENNReal.tendsto_ofReal
            (((tendsto_const_nhds.sub (hlim y hy)).norm.pow 2).mul_const _)
      _ ≤ liminf (fun j => ∫⁻ y in U,
            ENNReal.ofReal (‖F0 y - F (σ j) y‖ ^ 2 * Real.exp (-φ m y))) atTop :=
          lintegral_liminf_le' fun j => hmeas (hF _).continuousOn m
      _ ≤ A := by
          refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
          filter_upwards [eventually_ge_atTop m] with j hj
          refine le_trans (setLIntegral_mono' hU.measurableSet fun y hy => ?_) (hest (σ j))
          refine ENNReal.ofReal_le_ofReal ?_
          have := hanti y hy (hj.trans (hσ j))
          gcongr
  refine ⟨f, hfd, ?_⟩
  have e : ∀ y, ENNReal.ofReal (‖F0 y - f y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) =
      ⨆ k, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ k y)) := by
    intro y
    rw [ENNReal.mul_iSup]
    exact iSup_congr fun k => (ENNReal.ofReal_mul (by positivity)).symm
  simp_rw [e]
  rw [lintegral_iSup' (hmeas hfd.continuousOn)]
  · exact iSup_le hm
  · filter_upwards [ae_restrict_mem hU.measurableSet] with y hy a b hab
    refine ENNReal.ofReal_le_ofReal ?_
    have := hanti y hy hab
    gcongr

theorem hormander_limit : ∀ {n : ℕ} {U : Set (V n)}, IsOpen U → ∀ (e : V n → ℝ), ContDiffOn ℝ ∞ e U → (∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re) → (∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a}) → ∀ (φ : ℕ → V n → ℝ), (∀ k, ContDiffOn ℝ ∞ (φ k) U) → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → (∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y) → ∀ (F0 : V n → ℂ), ContDiffOn ℝ ∞ F0 U → ∀ (h : V n → ℝ≥0∞), Measurable h → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → ∀ A : ℝ≥0∞, (∀ k, ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ k y)) ≤ A) → ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧ ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  intro n U hU e he hel hec φ hφ hφl hdec F0 hF0 h hh hb A hA
  by_cases hAt : A = ⊤
  · exact ⟨0, differentiableOn_const 0, hAt ▸ le_top⟩
  choose F hF hest using fun k => ReciprocityTheory.ChartRestriction.G.AR.Up.HE.hormander_open hU e he hel hec (φ k)
    (hφ k) (hφl k) F0 hF0 h hh (hb k)
  refine exists_limit hU (fun j => {y | y ∈ U ∧ e y ≤ (j : ℝ)}) (fun j => hec j)
    (fun j y hy => hy.1) (fun y hy => ?_) (fun k => (hφ k).continuousOn) hdec hF0.continuousOn hAt
    hF fun k => (hest k).trans (hA k)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (e y)] with j hj
  exact ⟨hy, hj⟩

end GlobalTheory.HormanderLimit
