import Mathlib
open MeasureTheory Metric Filter Topology

namespace GlobalTheory

theorem schwartz_weighted_bound_of_cover {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (g : SchwartzMap D ℂ) (m n : ℕ) {K R δ η : ℝ} (hR : 0 < R) (t : Set D)
    (hcov : closedBall (0 : D) R ⊆ ⋃ y ∈ t, ball y δ)
    (hη : ∀ y ∈ t, ‖iteratedFDeriv ℝ n g y‖ ≤ η)
    (h1 : SchwartzMap.seminorm ℂ (m + 1) n g ≤ K) (h2 : SchwartzMap.seminorm ℂ 0 (n + 1) g ≤ K) :
    ∀ x : D, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n g x‖ ≤ max (K / R) (R ^ m * (η + K * δ)) := by
  have hlip : ∀ x y : D, ‖iteratedFDeriv ℝ n g y - iteratedFDeriv ℝ n g x‖ ≤ K * ‖y - x‖ := by
    intro x y
    refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ) ?_ ?_ convex_univ
      trivial trivial
    · intro z _
      exact ((g.smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)) z
    · intro z _
      rw [norm_fderiv_iteratedFDeriv]
      exact (g.norm_iteratedFDeriv_le_seminorm ℂ (n + 1) z).trans h2
  intro x
  rcases le_or_gt ‖x‖ R with hx | hx
  · apply le_max_of_le_right
    have hxm : x ∈ closedBall (0 : D) R := mem_closedBall_zero_iff.2 hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hxm)
    have hd : ‖x - y‖ < δ := by rw [← dist_eq_norm]; exact hxy
    have hK : 0 ≤ K := le_trans (apply_nonneg _ _) h2
    have hb : ‖iteratedFDeriv ℝ n g x‖ ≤ η + K * δ := by
      calc ‖iteratedFDeriv ℝ n g x‖
          = ‖iteratedFDeriv ℝ n g y + (iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y)‖ := by
            congr 1; abel
        _ ≤ ‖iteratedFDeriv ℝ n g y‖ + ‖iteratedFDeriv ℝ n g x - iteratedFDeriv ℝ n g y‖ :=
            norm_add_le _ _
        _ ≤ η + K * ‖x - y‖ := add_le_add (hη y hy) (hlip y x)
        _ ≤ η + K * δ := by gcongr
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx m) hb (norm_nonneg _)
      (pow_nonneg hR.le _)
  · apply le_max_of_le_left
    have hx0 : 0 < ‖x‖ := hR.trans hx
    rw [le_div_iff₀ hR]
    calc ‖x‖ ^ m * ‖iteratedFDeriv ℝ n g x‖ * R ≤ ‖x‖ ^ m * ‖iteratedFDeriv ℝ n g x‖ * ‖x‖ := by
          gcongr
      _ = ‖x‖ ^ (m + 1) * ‖iteratedFDeriv ℝ n g x‖ := by ring
      _ ≤ K := (g.le_seminorm ℂ (m + 1) n x).trans h1

end GlobalTheory

namespace GlobalTheory

theorem continuous_schwartz_of_pointwise_of_bounded {D S : Type} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [FiniteDimensional ℝ D] [TopologicalSpace S]
    (f : S → SchwartzMap D ℂ)
    (hpt : ∀ (n : ℕ) (x : D), Continuous fun s => iteratedFDeriv ℝ n (f s) x)
    (hbd : ∀ m n : ℕ, ∃ c : S → ℝ, Continuous c ∧ ∀ s, SchwartzMap.seminorm ℂ m n (f s) ≤ c s) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro s₀
  unfold ContinuousAt
  rw [(schwartz_withSeminorms ℂ D ℂ).tendsto_nhds]
  rintro ⟨m, n⟩ ε hε
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  obtain ⟨c1, hc1, hb1⟩ := hbd (m + 1) n
  obtain ⟨c2, hc2, hb2⟩ := hbd 0 (n + 1)
  have hc10 : 0 ≤ c1 s₀ := le_trans (apply_nonneg _ _) (hb1 s₀)
  have hc20 : 0 ≤ c2 s₀ := le_trans (apply_nonneg _ _) (hb2 s₀)
  set K : ℝ := (2 * c1 s₀ + 1) + (2 * c2 s₀ + 1) with hKdef
  have hK : 0 ≤ K := by positivity
  set R : ℝ := (2 * K + 1) / ε with hRdef
  have hR : 0 < R := by positivity
  set δ : ℝ := ε / (4 * (R ^ m * K + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  set η : ℝ := ε / (4 * (R ^ m + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨t, -, htf, hcov⟩ := (isCompact_closedBall (0 : D) R).finite_cover_balls hδ
  have ev1 : ∀ᶠ s in 𝓝 s₀, c1 s < c1 s₀ + 1 :=
    (hc1.tendsto s₀).eventually_lt_const (lt_add_one _)
  have ev2 : ∀ᶠ s in 𝓝 s₀, c2 s < c2 s₀ + 1 :=
    (hc2.tendsto s₀).eventually_lt_const (lt_add_one _)
  have ev3 : ∀ᶠ s in 𝓝 s₀, ∀ y ∈ t,
      ‖iteratedFDeriv ℝ n (f s) y - iteratedFDeriv ℝ n (f s₀) y‖ < η := by
    refine (Filter.eventually_all_finite htf).2 fun y _ => ?_
    have := Metric.tendsto_nhds.1 ((hpt n y).tendsto s₀) η hη
    simpa [dist_eq_norm] using this
  filter_upwards [ev1, ev2, ev3] with s h1 h2 h3
  have hD : ∀ k (x : D), iteratedFDeriv ℝ k (⇑(f s - f s₀)) x
      = iteratedFDeriv ℝ k (f s) x - iteratedFDeriv ℝ k (f s₀) x := by
    intro k x
    have hc : (⇑(f s - f s₀)) = ⇑(f s) - ⇑(f s₀) := by ext z; simp
    rw [hc]
    exact iteratedFDeriv_sub_apply (((f s).smooth k).contDiffAt) (((f s₀).smooth k).contDiffAt)
  have hs1 : SchwartzMap.seminorm ℂ (m + 1) n (f s - f s₀) ≤ K := by
    have := map_sub_le_add (SchwartzMap.seminorm ℂ (m + 1) n) (f s) (f s₀)
    have := hb1 s; have := hb1 s₀; have := hb2 s; have := hb2 s₀
    have : 0 ≤ c2 s₀ := hc20
    linarith
  have hs2 : SchwartzMap.seminorm ℂ 0 (n + 1) (f s - f s₀) ≤ K := by
    have := map_sub_le_add (SchwartzMap.seminorm ℂ 0 (n + 1)) (f s) (f s₀)
    have := hb1 s; have := hb1 s₀; have := hb2 s; have := hb2 s₀
    linarith
  have hpts : ∀ y ∈ t, ‖iteratedFDeriv ℝ n (⇑(f s - f s₀)) y‖ ≤ η := by
    intro y hy; rw [hD]; exact (h3 y hy).le
  have hbound := schwartz_weighted_bound_of_cover (f s - f s₀) m n hR t hcov hpts hs1 hs2
  have hle := SchwartzMap.seminorm_le_bound ℂ m n (f s - f s₀)
    (le_max_of_le_left (div_nonneg hK hR.le)) hbound
  refine lt_of_le_of_lt hle (max_lt ?_ ?_)
  · rw [div_lt_iff₀ hR, hRdef]
    field_simp
    nlinarith
  · have hRm : 0 ≤ R ^ m := pow_nonneg hR.le _
    have e1 : R ^ m * η ≤ ε / 4 := by
      rw [hηdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have e2 : R ^ m * (K * δ) ≤ ε / 4 := by
      rw [hδdef, ← mul_assoc, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 ≤ R ^ m * K := mul_nonneg hRm hK
      nlinarith
    nlinarith

end GlobalTheory
