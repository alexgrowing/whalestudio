import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice

open Matrix Filter Topology Metric
open scoped ComplexOrder

namespace GlobalTheory.ThetaGauss

theorem exists_entire_quot {N h : ℂ → ℂ} (hN : Differentiable ℂ N) (hh : Differentiable ℂ h)
    (h0 : ∃ s, h s ≠ 0)
    (hb : ∀ s₀, h s₀ = 0 → ∃ C : ℝ, ∀ᶠ s in 𝓝[≠] s₀, ‖N s‖ ≤ C * ‖h s‖) :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ s, k s * h s = N s := by
  have hne : ∀ s₀, ∀ᶠ s in 𝓝[≠] s₀, h s ≠ 0 := fun s₀ => by
    refine (hh.analyticAt s₀).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hz => ?_
    obtain ⟨s, hs⟩ := h0
    exact hs ((hh.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ s₀) hz (Set.mem_univ s))
  let q : ℂ → ℂ := fun s => N s / h s
  have hq : ∀ s, h s ≠ 0 → DifferentiableAt ℂ q s := fun s hs => (hN s).div (hh s) hs
  let k : ℂ → ℂ := fun s => limUnder (𝓝[≠] s) q
  have hk : ∀ s, h s ≠ 0 → k s = q s := fun s hs =>
    ((hq s hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hd : Differentiable ℂ k := by
    intro s₀
    by_cases hs : h s₀ = 0
    · obtain ⟨C, hC⟩ := hb s₀ hs
      obtain ⟨U, hU, hU'⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hC.and (hne s₀))
      have h1 : DifferentiableOn ℂ (Function.update q s₀ (limUnder (𝓝[≠] s₀) q)) U := by
        refine Complex.differentiableOn_update_limUnder_of_bddAbove hU
          (fun s hs => (hq s (hU' ⟨hs.1, hs.2⟩).2).differentiableWithinAt) ⟨C, ?_⟩
        rintro _ ⟨s, hs, rfl⟩
        have := hU' ⟨hs.1, hs.2⟩
        simp only [Function.comp, q, norm_div]
        rw [div_le_iff₀ (norm_pos_iff.2 this.2)]
        exact this.1
      refine (h1.differentiableAt hU).congr_of_eventuallyEq ?_
      filter_upwards [hU] with s hs
      by_cases e : s = s₀
      · subst e; simp [k]
      · rw [Function.update_of_ne e, hk s (hU' ⟨hs, e⟩).2]
    · refine (hq s₀ hs).congr_of_eventuallyEq ?_
      filter_upwards [(hh s₀).continuousAt.eventually_ne hs] with s hs using hk s hs
  refine ⟨k, hd, fun s₀ => ?_⟩
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] s₀)
    (((hd s₀).mul (hh s₀)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hN s₀).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [hne s₀] with s hs
  simp only [Pi.mul_apply]
  rw [hk s hs, div_mul_cancel₀ _ hs]

theorem exists_deriv_sq_quot {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ s, h s ≠ 0)
    (hm : ∀ s, h s = 0 → deriv h s = 0) :
    ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ s, k s * h s = deriv h s ^ 2 := by
  refine exists_entire_quot (hh.deriv.pow 2) hh h0 fun s₀ hs₀ => ?_
  have hnz : ¬ ∀ᶠ s in 𝓝 s₀, h s = 0 := fun hz => by
    obtain ⟨s, hs⟩ := h0
    exact hs ((hh.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ s₀) hz (Set.mem_univ s))
  obtain ⟨n, u, hu, hu0, he⟩ := (hh.analyticAt s₀).exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [smul_eq_mul] at he
  have hder : ∀ᶠ s in 𝓝 s₀, deriv h s = n * (s - s₀) ^ (n - 1) * u s + (s - s₀) ^ n * deriv u s := by
    filter_upwards [he.eventually_nhds, hu.eventually_analyticAt] with s hs hus
    rw [Filter.EventuallyEq.deriv_eq (f := fun s => (s - s₀) ^ n * u s) hs]
    have := (((hasDerivAt_id s).sub_const s₀).pow n).mul hus.differentiableAt.hasDerivAt
    simpa [Pi.mul_def] using this.deriv
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    rcases n with _ | _ | m
    · have := he.self_of_nhds; simp [hs₀] at this; exact absurd this.symm hu0
    · have := hder.self_of_nhds; simp [hm _ hs₀] at this; exact absurd this.symm hu0
    · exact ⟨m, rfl⟩
  let w : ℂ → ℂ := fun s => (s - s₀) ^ m * (((m + 2 : ℕ) : ℂ) * u s + (s - s₀) * deriv u s) ^ 2 / u s
  have hw : ContinuousAt w s₀ := by
    have := hu.continuousAt
    have := hu.deriv.continuousAt
    refine ContinuousAt.div ?_ hu.continuousAt hu0
    fun_prop
  refine ⟨‖w s₀‖ + 1, Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_⟩
  filter_upwards [he, hder, hu.continuousAt.eventually_ne hu0,
    hw.norm.eventually (ge_mem_nhds (lt_add_one _))] with s h1 h2 h3 h4
  have : deriv h s ^ 2 = w s * h s := by
    rw [h1, h2]; simp only [w, show m + 2 - 1 = m + 1 from rfl]; field_simp; ring
  rw [this, norm_mul]
  gcongr

theorem norm_deriv_sq_le {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hm : ∀ s, h s = 0 → deriv h s = 0) {r M δ : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) (hδ : 0 < δ)
    (hM : ∀ t ∈ closedBall (0 : ℂ) 1, ‖h t‖ ≤ M) (hl : ∀ t ∈ sphere (0 : ℂ) r, δ ≤ ‖h t‖) :
    ‖deriv h 0 ^ 2‖ ≤ (2 * M) ^ 2 / δ * ‖h 0‖ := by
  obtain ⟨k, hk, hk'⟩ := exists_deriv_sq_quot hh
    ⟨r, norm_pos_iff.1 (hδ.trans_le (hl _ (by simp [hr.le])))⟩ hm
  rw [← hk', norm_mul]
  gcongr
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball 0 r) isBounded_ball
    hk.diffContOnCl (fun t ht => ?_) (subset_closure (mem_ball_self hr))
  rw [frontier_ball _ hr.ne'] at ht
  have h1 : ‖deriv h t‖ ≤ M / (1 / 2) := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num) hh.diffContOnCl
      fun z hz => hM z ?_
    rw [mem_sphere] at ht hz
    rw [mem_closedBall]
    linarith [dist_triangle z t 0]
  rw [le_div_iff₀ hδ]
  calc ‖k t‖ * δ ≤ ‖k t‖ * ‖h t‖ := by gcongr; exact hl t ht
    _ = ‖deriv h t‖ ^ 2 := by rw [← norm_mul, hk', norm_pow]
    _ ≤ _ := by gcongr; linarith

variable {g : ℕ}

theorem analytic_of_diff {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) :
    AnalyticOnNhd ℂ f Set.univ :=
  ReciprocityTheory.AnForm.Osgood.osgood g _ f isOpen_univ hf.differentiableOn

noncomputable def transl {K : Type} [TopologicalSpace K] {f : (Fin g → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (γ : C(K, Fin g → ℂ)) (z : Fin g → ℂ) : C(K, ℂ) :=
  ⟨fun k => f (z + γ k), hf.continuous.comp (continuous_const.add γ.continuous)⟩

@[simp] theorem transl_apply {K : Type} [TopologicalSpace K] {f : (Fin g → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (γ : C(K, Fin g → ℂ)) (z : Fin g → ℂ) (k : K) :
    transl hf γ z k = f (z + γ k) := rfl

theorem differentiable_transl {K : Type} [TopologicalSpace K] [CompactSpace K]
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (γ : C(K, Fin g → ℂ)) :
    Differentiable ℂ (transl hf γ) := by
  intro z
  have hc : Continuous (fderiv ℂ f) :=
    continuousOn_univ.1 (analytic_of_diff hf).fderiv.continuousOn
  let L : (Fin g → ℂ) →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun h => ⟨fun k => fderiv ℂ f (z + γ k) h, by fun_prop⟩
      map_add' := fun a b => by ext k; simp
      map_smul' := fun a b => by ext k; simp }
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall z (‖γ‖ + 1)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall z (‖γ‖ + 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hmem : ∀ k, ∀ h ∈ ball (0 : Fin g → ℂ) 1, z + γ k + h ∈ closedBall z (‖γ‖ + 1) := by
    intro k h hh
    rw [mem_ball_zero_iff] at hh
    rw [mem_closedBall, dist_eq_norm, show z + γ k + h - z = γ k + h by abel]
    linarith [norm_add_le (γ k) h, γ.norm_coe_le_norm k]
  have hM : 0 ≤ M₁ + M₁ + M₂ := by
    have := (norm_nonneg _).trans (hM₁ z (mem_closedBall_self (by positivity)))
    have := (norm_nonneg _).trans (hM₂ z (mem_closedBall_self (by positivity)))
    positivity
  refine HasFDerivAt.differentiableAt (f' := LinearMap.toContinuousLinearMap L) ?_
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h => ‖h‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id (by norm_num))
  refine Asymptotics.IsBigO.of_bound (M₁ + M₁ + M₂) ?_
  filter_upwards [ball_mem_nhds 0 one_pos] with h hh
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun k => ?_
  have key := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    (f := fun h => f (z + γ k + h) - fderiv ℂ f (z + γ k) h) (c := 0) (z := h) (R₁ := 1)
    (R₂ := M₁ + M₁ + M₂) (n := 1) (by fun_prop) (fun y hy => ?_) ?_ hh
  · simp only [dist_eq_norm, add_zero, map_zero, sub_zero, div_one] at key
    simp only [norm_pow, norm_norm]
    refine le_trans (le_of_eq ?_) key
    congr 1
    change f (z + h + γ k) - f (z + γ k) - fderiv ℂ f (z + γ k) h = _
    rw [add_right_comm]; ring
  · simp only [mem_closedBall, dist_eq_norm, add_zero, map_zero, sub_zero]
    have h1 := hM₁ _ (hmem k y hy)
    have h2 := hM₁ _ (hmem k 0 (by simp))
    have h3 := hM₂ _ (hmem k 0 (by simp))
    rw [add_zero] at h2 h3
    have h4 : ‖fderiv ℂ f (z + γ k) y‖ ≤ M₂ := by
      refine ((fderiv ℂ f (z + γ k)).le_opNorm y).trans ?_
      rw [mem_ball_zero_iff] at hy
      nlinarith [norm_nonneg y, norm_nonneg (fderiv ℂ f (z + γ k))]
    linarith [norm_sub_le (f (z + γ k + y) - fderiv ℂ f (z + γ k) y) (f (z + γ k)),
      norm_sub_le (f (z + γ k + y)) (fderiv ℂ f (z + γ k) y)]
  · have := hasFDerivAt_iff_isLittleO_nhds_zero.1 (hf (z + γ k)).hasFDerivAt
    simp only [add_zero, map_zero, sub_zero, pow_one]
    refine (this.congr_left fun y => by ring).norm_right

theorem hasDerivAt_line {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (x v : Fin g → ℂ) (t : ℂ) :
    HasDerivAt (fun t : ℂ => f (x + t • v)) (fderiv ℂ f (x + t • v) v) t := by
  have h : HasDerivAt (fun t : ℂ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf _).hasFDerivAt.comp_hasDerivAt t h

theorem not_eventually_zero {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ s, h s ≠ 0) (s₀ : ℂ) :
    ¬ ∀ᶠ s in 𝓝 s₀, h s = 0 := fun hz => by
  obtain ⟨s, hs⟩ := h0
  exact hs ((hh.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ s₀) hz (Set.mem_univ s))

theorem exists_sphere {p : ℂ → Prop} (hp : ∀ᶠ t in 𝓝[≠] (0 : ℂ), p t) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ ∀ t ∈ sphere (0 : ℂ) r, p t := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hp
  obtain ⟨ε, hε, h⟩ := hp
  refine ⟨min (ε / 2) (1 / 2), by positivity, min_le_right _ _, fun t ht => h ?_ ?_⟩
  · rw [mem_sphere] at ht
    rw [ht]; exact (min_le_left _ _).trans_lt (by linarith)
  · rintro rfl
    simp only [mem_sphere, dist_self] at ht
    exact absurd ht (ne_of_lt (by positivity))

theorem bound_on_line {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (v : Fin g → ℂ)
    (hm : ∀ a, θ a = 0 → fderiv ℂ θ a v = 0) (z w : Fin g → ℂ) (h0 : ∃ s : ℂ, θ (z + s • w) ≠ 0) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖fderiv ℂ θ (z + s • w) v ^ 2‖ ≤ C * ‖θ (z + s • w)‖ := by
  let K : Set ℂ := closedBall 0 1
  let γ : C(K, Fin g → ℂ) := ⟨fun t => (t : ℂ) • v, by fun_prop⟩
  let Φ : ℂ → C(K, ℂ) := fun s => transl hθ γ (z + s • w)
  have hΦ : Differentiable ℂ Φ := (differentiable_transl hθ γ).comp (by fun_prop)
  have hnz : ¬ ∀ᶠ s in 𝓝 (0 : ℂ), Φ s = 0 := fun hz =>
    not_eventually_zero (h := fun s => θ (z + s • w)) (by fun_prop) h0 0 (hz.mono fun s hs => by
      simpa [Φ, γ] using congrArg (fun F : C(K, ℂ) => F ⟨0, by simp [K]⟩) hs)
  obtain ⟨n, G, hG, hG0, he⟩ := (hΦ.analyticAt 0).exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [sub_zero] at he
  let F : ℂ → ℂ → ℂ := fun s t => (s ^ n)⁻¹ * θ (z + s • w + t • v)
  have hFd : ∀ s, Differentiable ℂ (F s) := fun s => by fun_prop
  have hF : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ t : K, F s t = G s t := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0 t
    have := congrArg (fun F : C(K, ℂ) => F t) hs
    simp only [Φ, γ, transl_apply, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul] at this
    simp only [F]
    rw [this, inv_mul_cancel_left₀ (pow_ne_zero _ hs0)]
  have hclose : ∀ ε > 0, ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ t : K, ‖F s t - G 0 t‖ < ε := fun ε hε => by
    filter_upwards [hF, ((Metric.tendsto_nhds.1 hG.continuousAt) ε hε).filter_mono
      nhdsWithin_le_nhds] with s hs hs' t
    rw [hs, ← dist_eq_norm]
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt hs'
  classical
  let g₀ : ℂ → ℂ := fun t => if h : t ∈ K then G 0 ⟨t, h⟩ else 0
  have hg₀ : ∀ t : K, g₀ t = G 0 t := fun t => by simp [g₀]
  have hu : TendstoUniformlyOn F g₀ (𝓝[≠] 0) K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hclose ε hε] with s hs t ht
    rw [dist_comm, dist_eq_norm, hg₀ ⟨t, ht⟩]
    exact hs ⟨t, ht⟩
  have hgd : DifferentiableOn ℂ g₀ (ball 0 1) :=
    (hu.mono ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun s => (hFd s).differentiableOn) isOpen_ball
  have hgc : ContinuousOn g₀ K :=
    hu.continuousOn (Eventually.of_forall fun s => (hFd s).continuous.continuousOn).frequently
  have hga := hgd.analyticOnNhd isOpen_ball
  have hgne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g₀ t ≠ 0 := by
    refine (hga 0 (by simp)).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hz => hG0 ?_
    have h1 := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected
      (mem_ball_self one_pos) hz
    have h2 : Set.EqOn g₀ 0 K := h1.of_subset_closure hgc continuousOn_const
      ball_subset_closedBall (by rw [closure_ball _ one_ne_zero])
    ext t
    rw [← hg₀]; exact h2 t.2
  obtain ⟨r, hr, hr', hsph⟩ := exists_sphere hgne
  have hsub : sphere (0 : ℂ) r ⊆ K := sphere_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith))
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr.le) (hgc.mono hsub).norm
  have hδ : 0 < ‖g₀ t₀‖ / 2 := half_pos (norm_pos_iff.2 (hsph t₀ ht₀))
  refine ⟨(2 * (‖G 0‖ + 1)) ^ 2 / (‖g₀ t₀‖ / 2), ?_⟩
  filter_upwards [hclose _ hδ, hclose 1 one_pos, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (closedBall_mem_nhds (0 : ℂ) one_pos)] with s h1 h2 hs0 hs1
  have hsn : s ^ n ≠ 0 := pow_ne_zero _ hs0
  have hder : ∀ t, deriv (F s) t = (s ^ n)⁻¹ * fderiv ℂ θ (z + s • w + t • v) v := fun t =>
    ((hasDerivAt_line hθ (z + s • w) v t).const_mul _).deriv
  have key := norm_deriv_sq_le (hFd s) (fun t ht => by
      rw [hder, hm _ ((mul_eq_zero.1 ht).resolve_left (inv_ne_zero hsn)), mul_zero])
    hr hr' hδ (M := ‖G 0‖ + 1) (fun t ht => by
      have := h2 ⟨t, ht⟩
      linarith [norm_sub_norm_le (F s t) (G 0 ⟨t, ht⟩), (G 0).norm_coe_le_norm ⟨t, ht⟩])
    (fun t ht => by
      have h3 := h1 ⟨t, hsub ht⟩
      have h4 : ‖g₀ t₀‖ ≤ ‖g₀ t‖ := hmin ht
      rw [← hg₀, norm_sub_rev] at h3
      linarith [norm_sub_norm_le (g₀ t) (F s t)])
  rw [hder] at key
  simp only [F, zero_smul, add_zero, mul_pow, norm_mul] at key
  rw [← mul_pow] at key
  set C := (2 * (‖G 0‖ + 1)) ^ 2 / (‖g₀ t₀‖ / 2)
  have hC : 0 ≤ C := by positivity
  have hle : ‖s ^ n‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (by simpa using hs1)
  have hpos : 0 < ‖s ^ n‖ := norm_pos_iff.2 hsn
  rw [norm_pow, norm_inv] at key
  calc _ = ‖s ^ n‖ ^ 2 * (‖s ^ n‖⁻¹ ^ 2 * ‖fderiv ℂ θ (z + s • w) v ^ 2‖) := by field_simp
    _ ≤ ‖s ^ n‖ ^ 2 * (C * (‖s ^ n‖⁻¹ * ‖θ (z + s • w)‖)) := by gcongr
    _ = ‖s ^ n‖ * (C * ‖θ (z + s • w)‖) := by field_simp
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hle

theorem exists_mean : ∃ ℓ : C(Set.Icc (0 : ℝ) (2 * Real.pi), ℂ) →L[ℂ] ℂ,
    ∀ (f : C(Set.Icc (0 : ℝ) (2 * Real.pi), ℂ)) (k : ℂ → ℂ) (r : ℝ), Differentiable ℂ k →
      (∀ φ, f φ = k (circleMap 0 r φ)) → ℓ f = k 0 := by
  let p : ℝ → Set.Icc (0 : ℝ) (2 * Real.pi) := Set.projIcc 0 (2 * Real.pi) Real.two_pi_pos.le
  have hp : Continuous p := continuous_projIcc
  let L : C(Set.Icc (0 : ℝ) (2 * Real.pi), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ φ in (0 : ℝ)..(2 * Real.pi), f (p φ)
      map_add' := fun a b => intervalIntegral.integral_add
        ((a.continuous.comp hp).intervalIntegrable _ _) ((b.continuous.comp hp).intervalIntegrable _ _)
      map_smul' := fun a b => intervalIntegral.integral_smul a _ }
  have hL : ∀ f, ‖L f‖ ≤ |2 * Real.pi - 0| * ‖f‖ := fun f => by
    rw [mul_comm _ ‖f‖]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => f.norm_coe_le_norm _
  refine ⟨(2 * Real.pi)⁻¹ • L.mkContinuous _ hL, fun f k r hk hf => ?_⟩
  rw [← (hk.diffContOnCl (s := ball 0 |r|)).circleAverage, Real.circleAverage_def]
  change (2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), f (p φ) = _
  congr 1
  refine intervalIntegral.integral_congr fun φ hφ => ?_
  rw [Set.uIcc_of_le Real.two_pi_pos.le] at hφ
  simp only [hf, p, Set.projIcc_of_mem _ hφ]

theorem frequently_ne_zero {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (z) :
    (𝓝[{x | θ x ≠ 0}] z).NeBot := by
  refine frequently_mem_iff_neBot.1 fun h => ?_
  refine h0 (funext fun x => (analytic_of_diff hθ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) (h.mono fun y hy => ?_) (Set.mem_univ x))
  simpa using hy

theorem exists_entire_quot_of_lines {θ N : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (hN : Differentiable ℂ N) (h0 : θ ≠ 0)
    (hl : ∀ z w : Fin g → ℂ, (∃ s : ℂ, θ (z + s • w) ≠ 0) →
      ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ s, k s * θ (z + s • w) = N (z + s • w)) :
    ∃ ψ : (Fin g → ℂ) → ℂ, Differentiable ℂ ψ ∧ ∀ z, ψ z * θ z = N z := by
  obtain ⟨ℓ, hℓ⟩ := exists_mean
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  have hloc : ∀ a, ∃ Ψ : (Fin g → ℂ) → ℂ, ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ Ψ z ∧ Ψ z * θ z = N z := by
    intro a
    set w := z₀ - a with hw
    have hd : Differentiable ℂ fun s : ℂ => θ (a + s • w) := by fun_prop
    obtain ⟨r, hr, -, hsph⟩ := exists_sphere
      ((hd.analyticAt 0).eventually_eq_zero_or_eventually_ne_zero.resolve_left
        (not_eventually_zero hd ⟨1, by simpa [hw] using hz₀⟩ 0))
    let γ : C(Set.Icc (0 : ℝ) (2 * Real.pi), Fin g → ℂ) :=
      ⟨fun φ => circleMap 0 r φ • w, by fun_prop⟩
    have hunit : IsUnit (transl hθ γ a) :=
      (ContinuousMap.isUnit_iff_forall_ne_zero _).2 fun φ => hsph _ (circleMap_mem_sphere 0 hr.le φ)
    refine ⟨fun z => ℓ (transl hN γ z * Ring.inverse (transl hθ γ z)), ?_⟩
    filter_upwards [(differentiable_transl hθ γ).continuous.continuousAt.preimage_mem_nhds
      (Units.isOpen.mem_nhds hunit)] with z hz
    have hz' : IsUnit (transl hθ γ z) := hz
    refine ⟨ℓ.differentiableAt.comp z ((differentiable_transl hN γ z).mul
      ((differentiableAt_inverse hz').comp z (differentiable_transl hθ γ z))), ?_⟩
    have hne := (ContinuousMap.isUnit_iff_forall_ne_zero _).1 hz'
    obtain ⟨k, hk, hk'⟩ := hl z w ⟨_, hne ⟨0, le_rfl, Real.two_pi_pos.le⟩⟩
    rw [hℓ _ k r hk fun φ => ?_]
    · simpa using hk' 0
    · refine mul_right_cancel₀ (hne φ) ?_
      rw [← ContinuousMap.mul_apply, mul_assoc, Ring.inverse_mul_cancel _ hz', mul_one]
      exact (hk' _).symm
  choose Ψ hΨ using hloc
  let ψ : (Fin g → ℂ) → ℂ := fun z => limUnder (𝓝[{x | θ x ≠ 0}] z) (fun x => N x / θ x)
  have he : ∀ a, ∀ᶠ z in 𝓝 a, ψ z = Ψ a z := fun a => by
    filter_upwards [hΨ a, (hΨ a).eventually_nhds] with z h1 h2
    haveI := frequently_ne_zero hθ h0 z
    refine Tendsto.limUnder_eq ((h1.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_)
    filter_upwards [h2.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hy0
    rw [← hy.2, mul_div_cancel_right₀ _ hy0]
  refine ⟨ψ, fun a => (hΨ a).self_of_nhds.1.congr_of_eventuallyEq (he a), fun a => ?_⟩
  rw [(he a).self_of_nhds, (hΨ a).self_of_nhds.2]

theorem exists_fderiv_sq_quot {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (v : Fin g → ℂ) (hD : Differentiable ℂ fun z => fderiv ℂ θ z v)
    (hm : ∀ a, θ a = 0 → fderiv ℂ θ a v = 0) :
    ∃ ψ : (Fin g → ℂ) → ℂ, Differentiable ℂ ψ ∧ ∀ z, ψ z * θ z = fderiv ℂ θ z v ^ 2 := by
  refine exists_entire_quot_of_lines hθ (hD.pow 2) h0 fun z w hw => ?_
  have hl : Differentiable ℂ fun s : ℂ => z + s • w := by fun_prop
  refine exists_entire_quot (N := fun s => fderiv ℂ θ (z + s • w) v ^ 2) ((hD.comp hl).pow 2)
    (hθ.comp hl) hw fun s₀ _ => ?_
  have e : ∀ s : ℂ, z + s₀ • w + (s - s₀) • w = z + s • w := fun s => by
    rw [sub_smul]; abel
  obtain ⟨s₁, hs₁⟩ := hw
  obtain ⟨C, hC⟩ := bound_on_line hθ v hm (z + s₀ • w) w ⟨s₁ - s₀, by rwa [e]⟩
  have ht : Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun s hs => sub_ne_zero.2 hs⟩
    exact ((continuous_sub_right s₀).tendsto' s₀ 0 (sub_self _)).mono_left nhdsWithin_le_nhds
  exact ⟨C, (ht.eventually hC).mono fun s hs => by rwa [e] at hs⟩

theorem differentiable_fderiv_apply {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (v : Fin g → ℂ) : Differentiable ℂ fun z => fderiv ℂ θ z v :=
  (differentiableOn_univ.1 (analytic_of_diff hθ).fderiv.differentiableOn).clm_apply
    (differentiable_const v)

theorem fderiv_translate {f p : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (hp : Differentiable ℂ p) (a v : Fin g → ℂ) (j : (Fin g → ℂ) → ℂ) (l : ℂ)
    (hj : ∀ z (t : ℂ), j (z + t • v) = j z * Complex.exp (t * l))
    (h : ∀ z, f (z + a) = j z * p z) (z : Fin g → ℂ) :
    fderiv ℂ f (z + a) v = j z * (fderiv ℂ p z v + l * p z) := by
  have h1 := hasDerivAt_line hf (z + a) v 0
  have h2 := ((((hasDerivAt_id (0 : ℂ)).mul_const l).cexp).const_mul (j z)).mul
    (hasDerivAt_line hp z v 0)
  have e : (fun t : ℂ => f (z + a + t • v)) =
      (fun t : ℂ => j z * Complex.exp (id t * l)) * fun t : ℂ => p (z + t • v) := by
    ext t
    rw [add_right_comm, h, hj]; rfl
  rw [e] at h1
  have := h1.unique h2
  simp only [zero_smul, add_zero, id, zero_mul, Complex.exp_zero] at this
  rw [this]; ring

theorem eq_exp_of_ode {h h₁ h₂ : ℂ → ℂ} (hd : ∀ t, HasDerivAt h (h₁ t) t)
    (hd₁ : ∀ t, HasDerivAt h₁ (h₂ t) t) (c : ℂ) (he : ∀ t, h t * h₂ t - h₁ t ^ 2 = c * h t ^ 2)
    (h0 : h 0 ≠ 0) : ∃ α : ℂ, ∀ t, h t = h 0 * Complex.exp (α * t + c / 2 * t ^ 2) := by
  have hh : Differentiable ℂ h := fun t => (hd t).differentiableAt
  have hh₁ : Differentiable ℂ h₁ := fun t => (hd₁ t).differentiableAt
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 ((hh 0).continuousAt.eventually_ne h0)
  have hq : ∀ t ∈ ball (0 : ℂ) ε, HasDerivAt (fun t => h₁ t / h t - c * t) 0 t := fun t ht => by
    have := ((hd₁ t).div (hd t) (hb t ht)).sub ((hasDerivAt_id t).const_mul c)
    refine this.congr_deriv ?_
    have := hb t ht
    field_simp
    linear_combination he t
  refine ⟨h₁ 0 / h 0, ?_⟩
  set α := h₁ 0 / h 0 with hα
  have hc : ∀ t ∈ ball (0 : ℂ) ε, h₁ t / h t - c * t = α := fun t ht => by
    have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball _ _).isPreconnected
      (fun t ht => (hq t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hq t ht).deriv) ht (mem_ball_self hε)
    simpa using this
  have h1 : ∀ t, h₁ t - (α + c * t) * h t = 0 := by
    by_contra hn
    push_neg at hn
    refine not_eventually_zero (by fun_prop) hn 0 ?_
    filter_upwards [ball_mem_nhds 0 hε] with t ht
    rw [← hc t ht, sub_add_cancel, div_mul_cancel₀ _ (hb t ht), sub_self]
  have h2 : ∀ t, HasDerivAt (fun t => h t * Complex.exp (-(α * t + c / 2 * t ^ 2))) 0 t := fun t => by
    have := (hd t).mul ((((hasDerivAt_id t).const_mul α).add
      (((hasDerivAt_id t).pow 2).const_mul (c / 2))).neg.cexp)
    refine this.congr_deriv ?_
    simp only [id, Pi.neg_apply, Pi.add_apply, Pi.pow_apply]
    push_cast
    linear_combination Complex.exp (-(α * t + c / 2 * t ^ 2)) * h1 t
  intro t
  have := is_const_of_deriv_eq_zero (fun t => (h2 t).differentiableAt) (fun t => (h2 t).deriv) t 0
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, neg_zero,
    Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

theorem eq_zero_of_tendsto (L : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {u : (Fin g → ℂ) → ℝ} (hu : Continuous u) (hp : ∀ a ∈ L, ∀ z, u (z + a) = u z)
    (z w : Fin g → ℂ) (ht : Tendsto (fun n : ℕ => u (z + n • w)) atTop (𝓝 0)) : u z = 0 := by
  let Q := (Fin g → ℂ) ⧸ L.toAddSubgroup
  haveI : CompactSpace Q := by
    have := IsZLattice.isCompact_range_of_periodic L (QuotientAddGroup.mk : _ → Q)
      QuotientAddGroup.continuous_mk fun z w hw => by
        rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).2 hw, add_zero]
    rw [QuotientAddGroup.mk_surjective.range_eq] at this
    exact ⟨this⟩
  let U : Q → ℝ := Quotient.lift (fun x => u (z + x)) fun a b hab => by
    have hab' : -a + b ∈ L := QuotientAddGroup.leftRel_apply.1 hab
    have := hp _ hab' (z + a)
    rw [← this]; congr 1; abel
  have hU : Continuous U := Continuous.quotient_lift (by fun_prop) _
  have h1 := (mapClusterPt_zero_atTop_nsmul (QuotientAddGroup.mk w : Q)).continuousAt_comp
    hU.continuousAt
  have h2 : U 0 = u z := by
    change u (z + 0) = u z
    rw [add_zero]
  rw [h2] at h1
  exact eq_of_nhds_neBot (ClusterPt.mono h1 ht)

theorem exists_zero_fderiv_ne_zero : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.PosDef → ∀ (Λ : AddSubgroup (Fin g → ℂ)), DiscreteTopology Λ → (∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) ↔ v ∈ Λ) → ∀ (χ θ : (Fin g → ℂ) → ℂ), Differentiable ℂ θ → θ ≠ 0 → (∀ a ∈ Λ, ‖χ a‖ = 1) → (∀ a ∈ Λ, ∀ z, θ (z + a) = χ a * Complex.exp (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) * θ z) → ∀ v : Fin g → ℂ, v ≠ 0 → ∃ a, θ a = 0 ∧ fderiv ℂ θ a v ≠ 0 := by
  intro g Hm hH Λ hd hΛ χ θ hθ h0 hχ hθt v hv
  by_contra hm
  push_neg at hm
  have hD := differentiable_fderiv_apply hθ v
  obtain ⟨ψ, hψ, hψ'⟩ := exists_fderiv_sq_quot hθ h0 v hD hm
  set D : (Fin g → ℂ) → ℂ := fun z => fderiv ℂ θ z v with hDdef
  have hD₂ := differentiable_fderiv_apply hD v
  obtain ⟨c, hc⟩ := ThetaTranslSpan.exists_eq_smul hH Λ hΛ χ θ (fun z => fderiv ℂ D z v - ψ z) hχ
    hθ h0 hθt (hD₂.sub hψ) (fun a ha z => by
      set j : (Fin g → ℂ) → ℂ := fun z => χ a * Complex.exp
        (Real.pi * (star a ⬝ᵥ Hm.mulVec z) + Real.pi / 2 * (star a ⬝ᵥ Hm.mulVec a)) with hjdef
      set l : ℂ := Real.pi * (star a ⬝ᵥ Hm.mulVec v)
      have hj : ∀ z (t : ℂ), j (z + t • v) = j z * Complex.exp (t * l) := fun z t => by
        simp only [j, l, mulVec_add, dotProduct_add, mulVec_smul, dotProduct_smul, smul_eq_mul]
        rw [mul_assoc (χ a), ← Complex.exp_add]; congr 2; ring
      have hj0 : ∀ z, j z ≠ 0 := fun z =>
        mul_ne_zero (fun h => by simpa [h] using hχ a ha) (Complex.exp_ne_zero _)
      have hjc : Continuous j := by
        simp only [j, dotProduct, mulVec]
        fun_prop
      have e0 : ∀ z, θ (z + a) = j z * θ z := hθt a ha
      have e1 : ∀ z, D (z + a) = j z * (D z + l * θ z) := fderiv_translate hθ hθ a v j l hj e0
      have e2 := fderiv_translate hD (hD.add (hθ.const_mul l)) a v j l hj e1 z
      have e3 : fderiv ℂ (D + fun y => l * θ y) z v = fderiv ℂ D z v + l * D z := by
        rw [((hD z).hasFDerivAt.add ((hθ z).hasFDerivAt.const_mul l)).fderiv]; rfl
      have e4 : ψ (z + a) = j z * (ψ z + 2 * l * D z + l ^ 2 * θ z) := by
        haveI := frequently_ne_zero hθ h0 z
        have c1 : Continuous fun z => ψ (z + a) := hψ.continuous.comp (by fun_prop)
        have c2 : Continuous fun z => j z * (ψ z + 2 * l * D z + l ^ 2 * θ z) := by
          have := hψ.continuous; have := hD.continuous; have := hθ.continuous
          fun_prop
        refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[{x | θ x ≠ 0}] z)
          ((c1.tendsto z).mono_left nhdsWithin_le_nhds)
          ((c2.tendsto z).mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        refine mul_right_cancel₀ (mul_ne_zero (hj0 y) hy) ?_
        have a1 : ψ (y + a) * θ (y + a) = D (y + a) ^ 2 := hψ' _
        have a2 : ψ y * θ y = D y ^ 2 := hψ' _
        rw [e0, e1] at a1
        linear_combination a1 - j y ^ 2 * a2
      change _ = j z * _
      rw [e2, e3, e4]
      simp only [Pi.add_apply]
      ring)
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h0
  obtain ⟨α, hα⟩ := eq_exp_of_ode (hasDerivAt_line hθ z v) (hasDerivAt_line hD z v) c
    (fun t => by
      have a1 := congrFun hc (z + t • v)
      have a2 := hψ' (z + t • v)
      simp only [Pi.smul_apply, smul_eq_mul] at a1
      linear_combination θ (z + t • v) * a1 + a2) (by simpa using hz)
  simp only [zero_smul, add_zero] at hα
  obtain ⟨t₀, ht₀, hc₀⟩ : ∃ t₀ : ℂ, t₀ ≠ 0 ∧ (c / 2 * t₀ ^ 2).re ≤ 0 := by
    rcases le_total (c / 2).re 0 with h | h
    · exact ⟨1, one_ne_zero, by simpa using h⟩
    · exact ⟨Complex.I, Complex.I_ne_zero, by
        rw [Complex.I_sq, mul_neg_one, Complex.neg_re]; linarith⟩
  let B : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun x y => (star x ⬝ᵥ Hm.mulVec y).re
  have hB : ∀ x y, B x y = B y x := fun x y => by
    simp only [B]; rw [ThetaTranslSpan.herm_swap hH]; rfl
  have hBadd : ∀ x y, B (x + y) (x + y) = B x x + 2 * B y x + B y y := fun x y => by
    have := hB x y
    simp only [B, star_add, mulVec_add, add_dotProduct, dotProduct_add, Complex.add_re] at this ⊢
    linarith
  let u : (Fin g → ℂ) → ℝ := fun x => ‖θ x‖ * Real.exp (-(Real.pi / 2 * B x x))
  have huc : Continuous u := by
    have := hθ.continuous
    simp only [u, B, dotProduct, mulVec]
    fun_prop
  have hup : ∀ a ∈ Λ, ∀ x, u (x + a) = u x := fun a ha x => by
    simp only [u]
    rw [hθt a ha, norm_mul, norm_mul, hχ a ha, one_mul, Complex.norm_exp, hBadd, mul_right_comm,
      ← Real.exp_add, mul_comm]
    congr 2
    simp [B]
    ring
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Λ
  haveI hL : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨ThetaTranslSpan.span_eq_top hH Λ fun v => (hΛ v).1⟩
  set w := t₀ • v with hw
  have hw0 : w ≠ 0 := smul_ne_zero ht₀ hv
  have hpos : 0 < B w w := (Complex.pos_iff.1 (hH.dotProduct_mulVec_pos hw0)).1
  set A : ℝ := (α * t₀).re - Real.pi * B w z
  set β : ℝ := Real.pi / 2 * B w w - (c / 2 * t₀ ^ 2).re with hβ
  have hβ0 : 0 < β := by have := Real.pi_pos; have : 0 < Real.pi / 2 * B w w := by positivity
                         linarith
  have hun : ∀ n : ℕ, u (z + n • w) = u z * Real.exp (n * (A - β * n)) := fun n => by
    have hre : ∀ x : ℂ, ((n : ℂ) * x).re = n * x.re := fun x => by simp
    have b1 : B (n • w) z = n * B w z := by
      simp only [B]
      rw [star_nsmul, smul_dotProduct, nsmul_eq_mul, hre]
    have b2 : B (n • w) (n • w) = n * (n * B w w) := by
      simp only [B]
      rw [star_nsmul, smul_dotProduct, mulVec_smul, dotProduct_smul, nsmul_eq_mul, nsmul_eq_mul,
        hre, hre]
    have b3 : θ (z + n • w) = θ z * Complex.exp (n * (α * t₀) + n * (n * (c / 2 * t₀ ^ 2))) := by
      rw [hw, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hα]; congr 2; ring
    simp only [u]
    rw [hBadd, b1, b2, b3, norm_mul, Complex.norm_exp, mul_assoc, mul_assoc, ← Real.exp_add,
      ← Real.exp_add, Complex.add_re, hre, hre, hre]
    congr 2
    simp only [A, β]
    ring
  have hzero := eq_zero_of_tendsto L huc hup z w (by
    simp only [hun]
    rw [← mul_zero (u z)]
    refine Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)
    refine tendsto_natCast_atTop_atTop.atTop_mul_atBot₀ ?_
    exact tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hβ0)))
  exact absurd hzero (mul_pos (norm_pos_iff.2 hz) (Real.exp_pos _)).ne'

end GlobalTheory.ThetaGauss
