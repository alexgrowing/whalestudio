import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (coordDiv)

namespace LevelTowerAlt

variable {n : ℕ}

theorem frequently_ne (c y : Fin n → ℂ) : ∃ᶠ y' in 𝓝 y, ∀ k, y' k ≠ c k := by
  have h : Dense (Set.pi Set.univ fun k : Fin n => ({c k}ᶜ : Set ℂ)) :=
    dense_pi Set.univ fun k _ => dense_compl_singleton (c k)
  exact (mem_closure_iff_frequently.1 (h y)).mono fun y' hy' k => hy' k (Set.mem_univ k)

theorem eq_of_eventually_ne {β : Type*} [TopologicalSpace β] [T2Space β] {f g : (Fin n → ℂ) → β} (c : Fin n → ℂ)
    {y : Fin n → ℂ} (hf : ContinuousAt f y) (hg : ContinuousAt g y)
    (h : ∀ᶠ y' in 𝓝 y, (∀ k, y' k ≠ c k) → f y' = g y') : f y = g y :=
  tendsto_nhds_unique_of_frequently_eq hf hg (((frequently_ne c y).and_eventually h).mono fun _ h' => h'.2 h'.1)

theorem exists_div_coord {f : (Fin n → ℂ) → ℂ} {y₀ : Fin n → ℂ} (hf : AnalyticAt ℂ f y₀) (S : Finset (Fin n))
    (hz : ∀ᶠ y in 𝓝 y₀, y ∈ coordDiv S → f y = 0) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u y₀ ∧ ∀ᶠ y in 𝓝 y₀, f y = u y * ∏ i ∈ S, y i := by
  classical
  have hne : ∀ᶠ y in 𝓝 y₀, ∀ i, y₀ i ≠ 0 → y i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases h : y₀ i = 0
    · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
    · exact ((continuous_apply i).continuousAt.eventually_ne h).mono fun _ h' _ => h'
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hf.eventually_analyticAt.and (hz.and hne))
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  let A : (Fin n → ℂ) → Fin n → ℂ := fun z => y₀ + (r : ℂ) • z
  have hAd : Differentiable ℂ A := (differentiable_const _).add (differentiable_id.const_smul (r : ℂ))
  have hA : ∀ z ∈ ball (0 : Fin n → ℂ) 1, A z ∈ ball y₀ r := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    nlinarith
  have hkey : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i, (y₀ i = 0 → z i ≠ 0) → A z i ≠ 0 := by
    intro z hz i hi
    by_cases h : y₀ i = 0
    · show y₀ i + (r : ℂ) * z i ≠ 0
      rw [h, zero_add]
      exact mul_ne_zero hr' (hi h)
    · exact (hb _ (hA z hz)).2.2 i h
  have hAa : ∀ z, AnalyticAt ℂ A z := fun z => by
    have h1 : AnalyticAt ℂ ((fun _ : Fin n → ℂ => (r : ℂ)) • id) z := analyticAt_const.smul analyticAt_id
    exact analyticAt_const.add h1
  have hpd : ∀ z, AnalyticAt ℂ (fun z => ∏ i ∈ S, A z i) z := fun z =>
    Finset.analyticAt_fun_prod (𝕜 := ℂ) S (f := fun i z => A z i) fun i _ => analyticAt_pi_iff.1 (hAa z) i
  obtain ⟨G, hG, hGe⟩ := GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices.proof n
    (fun z => f (A z) / ∏ i ∈ S, A z i)
    (fun z hz => (AnalyticAt.fun_div (f := fun z => f (A z)) (g := fun z => ∏ i ∈ S, A z i)
      (AnalyticAt.comp (g := f) (f := A) (hb _ (hA z hz.1)).1 (hAa z)) (hpd z)
      (Finset.prod_ne_zero_iff.2 fun i _ => hkey z hz.1 i fun _ => hz.2 i)).differentiableAt.differentiableWithinAt)
    (by
      intro z hz i hi
      have h0 : Function.update z i 0 ∈ ball (0 : Fin n → ℂ) 1 := by
        rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
        intro k
        by_cases hk : k = i
        · subst hk
          simp
        · rw [Function.update_of_ne hk]
          exact hz k
      have hud : DifferentiableAt ℂ (Function.update z i) (0 : ℂ) := (hasFDerivAt_update z (0 : ℂ)).differentiableAt
      have hφ : DifferentiableAt ℂ (fun x : ℂ => f (A (Function.update z i x))) 0 :=
        DifferentiableAt.comp (g := fun w => f (A w)) 0
          ((hb _ (hA _ h0)).1.differentiableAt.comp _ (hAd _)) hud
      by_cases hc : i ∈ S ∧ y₀ i = 0
      · have hφ0 : f (A (Function.update z i 0)) = 0 :=
          (hb _ (hA _ h0)).2.1 ⟨i, hc.1, by simp [A, hc.2]⟩
        refine ⟨_, ((hasDerivAt_iff_tendsto_slope.1 hφ.hasDerivAt).div_const
          ((r : ℂ) * ∏ k ∈ S.erase i, A z k)).congr fun x => ?_⟩
        have h1 : ∏ k ∈ S.erase i, A (Function.update z i x) k = ∏ k ∈ S.erase i, A z k :=
          Finset.prod_congr rfl fun k hk => by
            simp only [A, Pi.add_apply, Pi.smul_apply, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        have h2 : A (Function.update z i x) i = r * x := by simp [A, hc.2]
        rw [← Finset.mul_prod_erase S _ hc.1, h1, h2, slope_def_field, hφ0, sub_zero, sub_zero, div_div]
        congr 1
        ring
      · refine ⟨_, tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto
          (hφ.continuousAt.div ((hpd _).continuousAt.comp hud.continuousAt) ?_))⟩
        refine Finset.prod_ne_zero_iff.2 fun k hk => hkey _ h0 k fun h => ?_
        have hki : k ≠ i := fun e => hc ⟨e ▸ hk, e ▸ h⟩
        rw [Function.update_of_ne hki]
        exact hi k hki)
  let B : (Fin n → ℂ) → Fin n → ℂ := fun y => (r : ℂ)⁻¹ • (y - y₀)
  have hBa : ∀ y, AnalyticAt ℂ B y := fun y => by
    have h1 : AnalyticAt ℂ ((fun _ : Fin n → ℂ => (r : ℂ)⁻¹) • (id - fun _ : Fin n → ℂ => y₀)) y :=
      analyticAt_const.smul (analyticAt_id.sub analyticAt_const)
    exact h1
  have hAB : ∀ y, A (B y) = y := fun y => by
    simp only [A, B, smul_smul, mul_inv_cancel₀ hr', one_smul, add_sub_cancel]
  have hB : ∀ y ∈ ball y₀ r, B y ∈ ball (0 : Fin n → ℂ) 1 := by
    intro y hy
    rw [mem_ball_iff_norm] at hy
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, inv_mul_lt_iff₀ hr,
      mul_one]
    exact hy
  have hu : ∀ y ∈ ball y₀ r, AnalyticAt ℂ (fun y => G (B y)) y := fun y hy =>
    AnalyticAt.comp (g := G) (f := B) (hG _ (hB y hy)) (hBa y)
  refine ⟨fun y => G (B y), hu _ (mem_ball_self hr), ?_⟩
  filter_upwards [ball_mem_nhds y₀ hr] with y hy
  refine eq_of_eventually_ne (f := f) (g := fun y => G (B y) * ∏ i ∈ S, y i) y₀ (hb y hy).1.continuousAt
    ((hu y hy).continuousAt.mul (continuous_finsetProd _ fun i _ => continuous_apply i).continuousAt) ?_
  filter_upwards [isOpen_ball.mem_nhds hy] with y' hy' hne'
  have h1 : ∀ i, B y' i ≠ 0 := fun i => mul_ne_zero (inv_ne_zero hr') (sub_ne_zero.2 (hne' i))
  have h2 : ∏ i ∈ S, y' i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => by
    have := hkey _ (hB y' hy') i fun _ => h1 i
    rwa [hAB] at this
  rw [hGe _ (hB y' hy') h1, hAB, div_mul_cancel₀ _ h2]

theorem prod_eq_zero_iff_coordDiv (S : Finset (Fin n)) (y : Fin n → ℂ) : ∏ i ∈ S, y i = 0 ↔ y ∈ coordDiv S :=
  Finset.prod_eq_zero_iff

theorem sum_log_eq (S : Finset (Fin n)) {y : Fin n → ℂ} (hy : y ∉ coordDiv S) :
    ∑ i ∈ S, Real.log (‖y i‖ ^ 2)⁻¹ = -2 * Real.log ‖∏ i ∈ S, y i‖ := by
  rw [norm_prod, Real.log_prod fun i hi => norm_ne_zero_iff.2 fun h => hy ⟨i, hi, h⟩, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_inv, Real.log_pow]
  push_cast
  ring

theorem exists_smooth_log_diff {Φ : (Fin n → ℂ) → Fin n → ℂ} {y₀ : Fin n → ℂ} (hΦ : AnalyticAt ℂ Φ y₀)
    {U : Set (Fin n → ℂ)} (hU : U ∈ 𝓝 y₀) (hinj : Set.InjOn Φ U) {S S' : Finset (Fin n)}
    (h : ∀ᶠ y in 𝓝 y₀, y ∈ coordDiv S ↔ Φ y ∈ coordDiv S') :
    ∃ q : (Fin n → ℂ) → ℝ, ContDiffAt ℝ ∞ q y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∉ coordDiv S →
      ∑ i ∈ S', Real.log (‖Φ y i‖ ^ 2)⁻¹ = ∑ i ∈ S, Real.log (‖y i‖ ^ 2)⁻¹ + q y := by
  obtain ⟨g, hga, hg0, hgr, hgl, -⟩ := exists_local_inverse hΦ hU hinj
  obtain ⟨u, hu, hue⟩ := exists_div_coord (f := fun y => ∏ i ∈ S', Φ y i)
    (Finset.analyticAt_fun_prod _ fun i _ => analyticAt_pi_iff.1 hΦ i) S
    (h.mono fun y hy hS => (prod_eq_zero_iff_coordDiv _ _).2 (hy.1 hS))
  have hgt : Tendsto g (𝓝 (Φ y₀)) (𝓝 y₀) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  obtain ⟨v, hv, hve⟩ := exists_div_coord (f := fun x => ∏ i ∈ S, g x i)
    (Finset.analyticAt_fun_prod _ fun i _ => analyticAt_pi_iff.1 hga i) S'
    (by
      filter_upwards [hgt.eventually h, hgr] with x h1 h2 h3
      rw [h2] at h1
      exact (prod_eq_zero_iff_coordDiv _ _).2 (h1.2 h3))
  have h1 : v (Φ y₀) * u y₀ = 1 := by
    refine eq_of_eventually_ne (f := fun y => v (Φ y) * u y) (g := fun _ => 1) 0
      ((hv.continuousAt.comp hΦ.continuousAt).mul hu.continuousAt) continuousAt_const ?_
    filter_upwards [hue, hΦ.continuousAt.tendsto.eventually hve, hgl] with y e1 e2 e3 hy
    rw [e3, e1, ← mul_assoc] at e2
    have hp : ∏ i ∈ S, y i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hy i
    exact mul_right_cancel₀ hp (by rw [← e2, one_mul])
  have hu0 : u y₀ ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have huR : AnalyticAt ℝ u y₀ := hu.restrictScalars
  refine ⟨fun y => -2 * Real.log ‖u y‖, contDiffAt_const.mul
    ((huR.contDiffAt.norm ℝ hu0).log (norm_ne_zero_iff.2 hu0)), ?_⟩
  filter_upwards [h, hue, hu.continuousAt.eventually_ne hu0] with y e1 e2 e3 hy
  have hp : ∏ i ∈ S, y i ≠ 0 := fun h0 => hy ((prod_eq_zero_iff_coordDiv _ _).1 h0)
  rw [sum_log_eq S' fun h' => hy (e1.2 h'), sum_log_eq S hy, e2, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 e3) (norm_ne_zero_iff.2 hp)]
  ring

theorem exists_smooth_glue {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) (E : (Fin n → ℂ) → ℝ)
    (h : ∀ y₀ ∈ U, ∃ q : (Fin n → ℂ) → ℝ, ContDiffAt ℝ ∞ q y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∉ coordDiv S → E y = q y) :
    ∃ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f U ∧ ∀ y ∈ U, y ∉ coordDiv S → E y = f y := by
  choose! q hq hqe using h
  refine ⟨fun y => q y y, fun y₀ hy₀ => ((hq y₀ hy₀).congr_of_eventuallyEq ?_).contDiffWithinAt,
    fun y hy => (hqe y hy).self_of_nhds⟩
  have hc : ∀ᶠ y in 𝓝 y₀, ContinuousAt (q y₀) y :=
    (((hq y₀ hy₀).of_le (m := 1) (by exact_mod_cast le_top)).eventually (by simp)).mono fun _ h => h.continuousAt
  filter_upwards [hU.mem_nhds hy₀, hc, (hqe y₀ hy₀).eventually_nhds] with y hy h1 h2
  refine eq_of_eventually_ne (f := q y) (g := q y₀) 0 (hq y hy).continuousAt h1 ?_
  filter_upwards [h2, hqe y hy] with y' e1 e2 hy'
  have hn : y' ∉ coordDiv S := fun ⟨i, _, hi⟩ => hy' i hi
  rw [← e1 hn, ← e2 hn]

end LevelTowerAlt
