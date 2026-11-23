import ReciprocityTheory.L2DbarEstimates.LeviForms.FixedA

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lintegral_ball_translate {n : ℕ} (y₀ : V n) (ρ : ℝ) (Φ : V n → ℝ≥0∞) :
    ∫⁻ y in ball (0 : V n) ρ, Φ (y₀ + y) = ∫⁻ y in ball y₀ ρ, Φ y := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  have h : ∀ y, (ball (0 : V n) ρ).indicator (fun y => Φ (y₀ + y)) y =
      (ball y₀ ρ).indicator Φ (y₀ + y) := fun y => by
    simp [Set.indicator, mem_ball, dist_eq_norm]
  simp_rw [h]
  exact lintegral_add_left_eq_self ((ball y₀ ρ).indicator Φ) y₀

theorem fx_tendsto_zero_of_weighted {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (hn : 1 ≤ n) (hV : VanishStatement n)
    (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (p : M) (hp : p ∈ e.source) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ball (z p) ρ ⊆ e.target) (c₀ C' Cb : ℝ) (hc₀ : 0 < c₀) (hC' : 0 < C')
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝[>] 0)) (u : ℕ → M → ℂ) (w : ℕ → M → ℝ)
    (hu : ∀ k, Measurable (u k)) (hw : ∀ k, Measurable (w k))
    (hdiff : ∀ k, DifferentiableOn ℂ (fun y => u k (e.symm y)) (ball (z p) ρ))
    (hlow : ∀ k, ∀ y ∈ ball (z p) ρ,
      c₀ * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)) ≤ w k (e.symm y))
    (hint : ∀ k, ∫⁻ x, ENNReal.ofReal (‖u k x‖ ^ 2 * w k x) ∂vol n z ≤ ENNReal.ofReal Cb) :
    Tendsto (fun k => u k p) atTop (𝓝 0) := by
  have hzp : e.symm (z p) = p := by rw [he hp]; exact e.left_inv hp
  have key := hV hn ρ C' (c₀⁻¹ * Cb) δ (fun k y => u k (e.symm (z p + y))) hρ hC' hδ ?_ ?_
  · simpa [hzp] using key
  · intro k
    refine (hdiff k).comp ((differentiableOn_const _).add differentiableOn_id) fun y hy => ?_
    simpa [mem_ball, dist_eq_norm] using hy
  · intro k
    have h1 := fx_lintegral_ball_translate (z p) ρ
      (fun y => ENNReal.ofReal (‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ))))
    simp only [add_sub_cancel_left] at h1
    rw [h1]
    set f' : M → ℝ≥0∞ := e.source.indicator fun x => ENNReal.ofReal (‖u k x‖ ^ 2 * w k x)
      with hf'
    have hf'm : Measurable f' :=
      (ENNReal.measurable_ofReal.comp (((hu k).norm.pow_const 2).mul (hw k))).indicator
        e.open_source.measurableSet
    have hchart := lintegral_vol_chart n z hz e he f' hf'm
      (fun x hx => by simp [hf', hx])
    calc ∫⁻ y in ball (z p) ρ,
          ENNReal.ofReal (‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)))
        ≤ ∫⁻ y in ball (z p) ρ, ENNReal.ofReal c₀⁻¹ * f' (e.symm y) := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          have hs : e.symm y ∈ e.source := e.map_target (hball hy)
          rw [hf', Set.indicator_of_mem hs, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc₀.le)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 := hlow k y hy
          have h3 : (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ)) ≤ c₀⁻¹ * w k (e.symm y) := by
            rw [le_inv_mul_iff₀ hc₀]; exact h2
          calc ‖u k (e.symm y)‖ ^ 2 * (C' * ‖y - z p‖ ^ 2 + δ k) ^ (-(n : ℝ))
              ≤ ‖u k (e.symm y)‖ ^ 2 * (c₀⁻¹ * w k (e.symm y)) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = _ := by ring
      _ = ENNReal.ofReal c₀⁻¹ * ∫⁻ y in ball (z p) ρ, f' (e.symm y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c₀⁻¹ * ∫⁻ y in e.target, f' (e.symm y) := by
          gcongr
      _ = ENNReal.ofReal c₀⁻¹ * ∫⁻ x, f' x ∂vol n z := by rw [hchart]
      _ ≤ ENNReal.ofReal c₀⁻¹ * ENNReal.ofReal Cb := by
          gcongr
          refine (lintegral_mono fun x => ?_).trans (hint k)
          exact Set.indicator_le_self _ _ x
      _ = ENNReal.ofReal (c₀⁻¹ * Cb) := (ENNReal.ofReal_mul (inv_nonneg.mpr hc₀.le)).symm

theorem fx_exists_ball_bounds {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph ph2 : M → ℝ)
    (hph : SmoothR n z ph) (hph2 : SmoothR n z ph2) (r : ℝ) (hr : 0 < r) (j : ℕ) (ε : ℝ)
    (hε : 0 < ε) (p : M) (hp : p ∈ zeroSet n g) (U : Set M) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source ∧
      ∃ ρ > 0, ∃ C1 > 0, ∃ A : ℝ, ball (z p) ρ ⊆ e.target ∧ ∀ y ∈ ball (z p) ρ,
        e.symm y ∈ U ∧ ev n g ph r (e.symm y) ≤ ε ^ 2 / 2 ∧
        ev n g ph r (e.symm y) ≤ C1 * ‖y - z p‖ ^ 2 ∧
        ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y) ≤ A := by
  obtain ⟨e, he, hpe⟩ := exists_chart n z hz p
  have hzp : z p ∈ e.target := by rw [he hpe]; exact e.map_source hpe
  have hsp : e.symm (z p) = p := by rw [he hpe]; exact e.left_inv hpe
  have hcs : ContinuousAt e.symm (z p) := e.continuousAt_symm hzp
  have hre : ∀ f : M → ℝ, SmoothR n z f → Continuous f := fun f hf =>
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hf)).congr fun x => by simp
  have hev0 : ev n g ph r p = 0 := fx_ev_eq_zero n g ph r p hp

  have hlip : ∀ i, ∃ c : ℝ, ∀ᶠ y in 𝓝 (z p), ‖g i (e.symm y)‖ ≤ c * ‖y - z p‖ := by
    intro i
    have hd : DifferentiableAt ℂ (fun y => g i (e.symm y)) (z p) :=
      (hg i e he).differentiableAt (e.open_target.mem_nhds hzp)
    obtain ⟨c, hc⟩ := hd.hasFDerivAt.isBigO_sub.bound
    refine ⟨c, hc.mono fun y hy => ?_⟩
    have h0 : g i (e.symm (z p)) = 0 := by rw [hsp]; exact hp i
    simpa [h0] using hy
  choose c hc using hlip
  have h1 : ∀ᶠ y in 𝓝 (z p), y ∈ e.target := e.open_target.mem_nhds hzp
  have h2 : ∀ᶠ y in 𝓝 (z p), e.symm y ∈ U := hcs.preimage_mem_nhds (by rw [hsp]; exact hU.mem_nhds hpU)
  have hevc : ContinuousAt (fun y => ev n g ph r (e.symm y)) (z p) :=
    (fx_continuous_ev n z hz g hg ph hph r).continuousAt.comp hcs
  have h3 : ∀ᶠ y in 𝓝 (z p), ev n g ph r (e.symm y) < ε ^ 2 / 2 := by
    refine hevc.eventually (gt_mem_nhds ?_)
    show ev n g ph r (e.symm (z p)) < _
    rw [hsp, hev0]; positivity
  have hψc : ContinuousAt (fun y => ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y)) (z p) :=
    (((hre _ hph2).add (continuous_const.mul (hre _ hph))).continuousAt).comp hcs
  have h4 : ∀ᶠ y in 𝓝 (z p), ph2 (e.symm y) + ((n : ℝ) + j) * ph (e.symm y) <
      ph2 p + ((n : ℝ) + j) * ph p + 1 := by
    refine hψc.eventually (gt_mem_nhds ?_)
    simp only [hsp]; linarith
  have hxc : ContinuousAt (fun y => Real.exp (-ph (e.symm y))) (z p) :=
    ((Real.continuous_exp.comp (hre _ hph).neg).continuousAt).comp hcs
  have h5 : ∀ᶠ y in 𝓝 (z p), Real.exp (-ph (e.symm y)) < Real.exp (-ph p) + 1 := by
    refine hxc.eventually (gt_mem_nhds ?_)
    simp only [hsp]; linarith
  have h6 : ∀ᶠ y in 𝓝 (z p), ∀ i, ‖g i (e.symm y)‖ ≤ c i * ‖y - z p‖ :=
    Filter.eventually_all.2 hc
  obtain ⟨ρ, hρ, hall⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (h3.and (h4.and (h5.and h6)))))
  set C1 : ℝ := (∑ i, c i ^ 2) * (Real.exp (-ph p) + 1) / r ^ 2 + 1 with hC1
  have hC1pos : 0 < C1 := by positivity
  refine ⟨e, he, hpe, ρ, hρ, C1, hC1pos, ph2 p + ((n : ℝ) + j) * ph p + 1,
    fun y hy => (hall y hy).1, fun y hy => ?_⟩
  obtain ⟨-, hU', h3', h4', h5', h6'⟩ := hall y hy
  refine ⟨hU', h3'.le, ?_, h4'.le⟩
  have hs : ∑ i, ‖g i (e.symm y)‖ ^ 2 ≤ (∑ i, c i ^ 2) * ‖y - z p‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h6' i) 2
  have hr2 : 0 < r ^ 2 := by positivity
  unfold ev
  rw [div_le_iff₀ hr2]
  have hsum0 : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc (∑ i, ‖g i (e.symm y)‖ ^ 2) * Real.exp (-ph (e.symm y))
      ≤ ((∑ i, c i ^ 2) * ‖y - z p‖ ^ 2) * (Real.exp (-ph p) + 1) :=
        mul_le_mul hs h5'.le (Real.exp_pos _).le (by positivity)
    _ ≤ C1 * ‖y - z p‖ ^ 2 * r ^ 2 := by
        rw [hC1, add_mul, add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_cancel_right₀ _ hr2.ne']
        nlinarith [sq_nonneg ‖y - z p‖, sq_nonneg r, mul_nonneg hsum0 (sq_nonneg ‖y - z p‖)]

end

end ReciprocityTheory.L2DbarEstimates.I
