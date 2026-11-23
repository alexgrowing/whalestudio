import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivF

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Set Filter
open scoped ENNReal

variable {n : ℕ}

private theorem countable_of_forall_exists_gap_above (S : Set ℝ) (h : ∀ t ∈ S, ∃ y, t < y ∧ ∀ u ∈ S, ¬ (t < u ∧ u < y)) :
    S.Countable := by
  classical
  have hq : ∀ t ∈ S, ∃ q : ℚ, t < q ∧ ∀ u ∈ S, ¬ (t < u ∧ u < q) := by
    intro t ht
    obtain ⟨y, hy, hyS⟩ := h t ht
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hy
    exact ⟨q, hq1, fun u hu h' => hyS u hu ⟨h'.1, h'.2.trans hq2⟩⟩
  choose! f hf1 hf2 using hq
  refine Set.MapsTo.countable_of_injOn (f := f) (Set.mapsTo_univ f S) ?_ Set.countable_univ
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact hf2 a ha b hb ⟨h1, by rw [hab]; exact hf1 b hb⟩
  · exact hf2 b hb a ha ⟨h1, by rw [← hab]; exact hf1 a ha⟩

private theorem volume_ball_inter_zeroSet_eq_zero_of_ne_zero {U : Set (V n)} {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) {z0 : V n}
    {R R' : ℝ} (hR' : 0 < R') (hRR : R' < R) (hball : ball z0 R ⊆ U) (hz0 : g z0 ≠ 0) :
    volume (ball z0 R' ∩ {z | g z = 0}) = 0 := by
  have hR : 0 < R := hR'.trans hRR
  have hcs : ∀ (u : ℝ) (w : V n), ((u : ℂ) • w) = u • w := fun u w => by
    first
      | exact Complex.coe_smul u w
      | exact (RCLike.real_smul_eq_coe_smul (K := ℂ) u w).symm
  have hmaps : ∀ t : ℝ, ∀ x : V n, t ∈ Ioo (0:ℝ) 1 → x ∈ ball z0 R →
      z0 + t • (x - z0) ∈ ball z0 R := by
    intro t x ht hx
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2.le) (norm_nonneg (x - z0))]
  have hO1 : IsOpen (Ioo (0:ℝ) 1 ×ˢ ball z0 R) := isOpen_Ioo.prod isOpen_ball
  have hFc : ContinuousOn (fun p : ℝ × V n => g (z0 + p.1 • (p.2 - z0))) (Ioo (0:ℝ) 1 ×ˢ ball z0 R) :=
    hg.continuousOn.comp (f := fun p : ℝ × V n => z0 + p.1 • (p.2 - z0))
      (Continuous.continuousOn (by fun_prop)) (fun p hp => hball (hmaps p.1 p.2 hp.1 hp.2))
  have hOpen := hFc.isOpen_inter_preimage hO1 (isOpen_compl_singleton (x := (0:ℂ)))
  obtain ⟨A, hAdef⟩ : ∃ A : Set (ℝ × V n), A = (Ioo (0:ℝ) 1 ×ˢ ball z0 R) \
      ((Ioo (0:ℝ) 1 ×ˢ ball z0 R) ∩ (fun p : ℝ × V n => g (z0 + p.1 • (p.2 - z0))) ⁻¹' {(0:ℂ)}ᶜ) :=
    ⟨_, rfl⟩
  have hA : MeasurableSet A := by
    rw [hAdef]
    exact hO1.measurableSet.diff hOpen.measurableSet
  have memA : ∀ t x, (t, x) ∈ A ↔ t ∈ Ioo (0:ℝ) 1 ∧ x ∈ ball z0 R ∧ g (z0 + t • (x - z0)) = 0 := by
    intro t x
    rw [hAdef]
    simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    tauto
  have hslice : ∀ x : V n, volume ((fun t : ℝ => (t, x)) ⁻¹' A) = 0 := by
    intro x
    by_cases hx : x ∈ ball z0 R
    · set v := x - z0 with hv
      have hvR : ‖v‖ < R := by
        rw [hv, ← dist_eq_norm]
        exact hx
      have hmpos : 0 < max ‖v‖ (R / 2) := lt_max_of_lt_right (by linarith)
      have hmR : max ‖v‖ (R / 2) < R := max_lt hvR (by linarith)
      set ρ := R / max ‖v‖ (R / 2) with hρ
      have hρ1 : 1 < ρ := (one_lt_div hmpos).mpr hmR
      have hDmaps : ∀ s ∈ ball (0:ℂ) ρ, z0 + s • v ∈ U := by
        intro s hs
        apply hball
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
        rw [Metric.mem_ball, dist_zero_right] at hs
        calc ‖s‖ * ‖v‖ ≤ ‖s‖ * max ‖v‖ (R / 2) :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
          _ < ρ * max ‖v‖ (R / 2) := mul_lt_mul_of_pos_right hs hmpos
          _ = R := div_mul_cancel₀ _ hmpos.ne'
      have hφd : DifferentiableOn ℂ (fun s : ℂ => g (z0 + s • v)) (ball (0:ℂ) ρ) :=
        hg.comp (f := fun s : ℂ => z0 + s • v) (Differentiable.differentiableOn (by fun_prop)) hDmaps
      have hφa := hφd.analyticOnNhd isOpen_ball
      have h0D : (0:ℂ) ∈ ball (0:ℂ) ρ := Metric.mem_ball_self (by linarith)
      have hφ0 : g (z0 + (0:ℂ) • v) ≠ 0 := by
        rw [zero_smul, add_zero]
        exact hz0
      have hpre : IsPreconnected (ball (0:ℂ) ρ) := (convex_ball (0:ℂ) ρ).isPreconnected
      have hiso : ∀ t : ℝ, t ∈ Ioo (0:ℝ) 1 →
          ∃ ε > 0, ∀ u : ℝ, t < u → u < t + ε → g (z0 + u • v) ≠ 0 := by
        intro t ht
        have htD : (t:ℂ) ∈ ball (0:ℂ) ρ := by
          rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
          linarith [ht.2]
        have hev : ∀ᶠ s in 𝓝[≠] (t:ℂ), g (z0 + s • v) ≠ 0 := by
          by_contra hne
          rw [Filter.not_eventually] at hne
          simp only [not_not] at hne
          have h5 := hφa.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre htD hne h0D
          exact hφ0 h5
        obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
        refine ⟨ε, hε, fun u hu1 hu2 => ?_⟩
        have h6 := hεp (y := (u:ℂ)) ?_ ?_
        · rwa [hcs] at h6
        · rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
          linarith
        · exact fun h => (ne_of_gt hu1) (Complex.ofReal_injective h)
      have hcount : Set.Countable {t : ℝ | t ∈ Ioo (0:ℝ) 1 ∧ g (z0 + t • v) = 0} := by
        refine countable_of_forall_exists_gap_above _ fun t ht => ?_
        obtain ⟨ε, hε, hεp⟩ := hiso t ht.1
        exact ⟨t + ε, by linarith, fun u hu h' => hεp u h'.1 h'.2 hu.2⟩
      have hsub : (fun t : ℝ => (t, x)) ⁻¹' A ⊆ {t : ℝ | t ∈ Ioo (0:ℝ) 1 ∧ g (z0 + t • v) = 0} := by
        intro t ht
        have h7 := (memA t x).mp ht
        exact ⟨h7.1, h7.2.2⟩
      exact measure_mono_null hsub (hcount.measure_zero _)
    · have h8 : (fun t : ℝ => (t, x)) ⁻¹' A = ∅ :=
        Set.subset_empty_iff.mp (fun t ht => (hx ((memA t x).mp ht).2.1).elim)
      rw [h8, measure_empty]
  have hprod : (volume.prod volume : Measure (ℝ × V n)) A = 0 := by
    rw [Measure.prod_apply_symm hA]
    simp only [hslice, lintegral_zero]
  rw [Measure.prod_apply hA] at hprod
  have hlow : ∀ t ∈ Ioo (R' / R) 1,
      volume (ball z0 R' ∩ {z | g z = 0}) ≤ volume (Prod.mk t ⁻¹' A) := by
    intro t ht
    have ht0 : 0 < t := lt_trans (div_pos hR' hR) ht.1
    have htR : R' < t * R := (div_lt_iff₀ hR).mp ht.1
    have hsub : (fun x : V n => x - z0) ⁻¹' ((fun y : V n => t • y) ⁻¹'
        ((fun w : V n => z0 + w) ⁻¹' (ball z0 R' ∩ {z | g z = 0}))) ⊆ Prod.mk t ⁻¹' A := by
      intro x hx
      simp only [Set.mem_preimage] at hx
      rw [Set.mem_preimage, memA]
      refine ⟨⟨ht0, ht.2⟩, ?_, hx.2⟩
      have h1 := hx.1
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0] at h1
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_mul_lt_mul_left (h1.trans htR) ht0.le
    have hti : 1 ≤ t⁻¹ := by
      have h2 := mul_inv_cancel₀ ht0.ne'
      nlinarith [mul_pos (inv_pos.mpr ht0) (sub_pos.mpr ht.2)]
    have hmeas : volume (ball z0 R' ∩ {z | g z = 0}) ≤ volume ((fun x : V n => x - z0) ⁻¹'
        ((fun y : V n => t • y) ⁻¹' ((fun w : V n => z0 + w) ⁻¹' (ball z0 R' ∩ {z | g z = 0})))) := by
      rw [show (fun x : V n => x - z0) = (fun x => x + -z0) from funext fun x => sub_eq_add_neg x z0,
        measure_preimage_add_right, Set.preimage_smul₀ ht0.ne', Measure.addHaar_smul,
        measure_preimage_add]
      refine le_mul_of_one_le_left (by positivity) ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_pos (pow_pos (inv_pos.mpr ht0) _)]
      first
        | exact one_le_pow₀ hti
        | exact one_le_pow_of_one_le' hti _
    exact hmeas.trans (measure_mono hsub)
  have hind : ∀ t, (Ioo (R' / R) 1).indicator (fun _ => volume (ball z0 R' ∩ {z | g z = 0})) t ≤
      volume (Prod.mk t ⁻¹' A) := by
    intro t
    by_cases ht : t ∈ Ioo (R' / R) 1
    · rw [Set.indicator_apply, if_pos ht]
      exact hlow t ht
    · rw [Set.indicator_apply, if_neg ht]
      positivity
  have hle : ∫⁻ t, (Ioo (R' / R) 1).indicator (fun _ => volume (ball z0 R' ∩ {z | g z = 0})) t ≤
      ∫⁻ t, volume (Prod.mk t ⁻¹' A) := lintegral_mono hind
  rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, hprod] at hle
  have hpos : ENNReal.ofReal (1 - R' / R) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le, sub_pos, div_lt_one hR]
    exact hRR
  exact (mul_eq_zero.mp (le_zero_iff.mp hle)).resolve_right hpos

theorem zero_null {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) :
    volume (U ∩ {z | g z = 0}) = 0 := by
  classical
  have hWopen : IsOpen {z : V n | ∀ᶠ y in 𝓝 z, g y = 0} := isOpen_setOf_eventually_nhds
  have hclosed : ∀ z ∈ U, z ∈ closure {z : V n | ∀ᶠ y in 𝓝 z, g y = 0} → ∀ᶠ y in 𝓝 z, g y = 0 := by
    intro z hz hzc
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
    by_contra hne
    have hex : ∃ z0 ∈ ball z (r / 4), g z0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (Metric.eventually_nhds_iff_ball.mpr ⟨r / 4, by linarith, h⟩)
    obtain ⟨z0, hz0, hgz0⟩ := hex
    rw [Metric.mem_ball] at hz0
    have hball : ball z0 (3 * r / 4) ⊆ U := by
      intro y hy
      apply hrU
      rw [Metric.mem_ball] at hy ⊢
      linarith [dist_triangle y z0 z]
    have hnull := volume_ball_inter_zeroSet_eq_zero_of_ne_zero hg (R := 3 * r / 4) (R' := 5 * r / 8) (by linarith) (by linarith) hball hgz0
    obtain ⟨w, hwW, hwz⟩ := Metric.mem_closure_iff.mp hzc (r / 4) (by linarith)
    obtain ⟨δ, hδ, hδw⟩ := Metric.eventually_nhds_iff_ball.mp hwW
    have hsub : ball w (min δ (r / 8)) ⊆ ball z0 (5 * r / 8) ∩ {z | g z = 0} := by
      intro y hy
      rw [Metric.mem_ball] at hy
      have hy1 : dist y w < δ := lt_of_lt_of_le hy (min_le_left _ _)
      have hy2 : dist y w < r / 8 := lt_of_lt_of_le hy (min_le_right _ _)
      refine ⟨?_, hδw y hy1⟩
      rw [Metric.mem_ball]
      linarith [dist_triangle y w z, dist_triangle y z z0, dist_comm z0 z, dist_comm z w]
    exact (Metric.measure_ball_pos volume w (lt_min hδ (by linarith))).ne' (measure_mono_null hsub hnull)
  have hWempty : ∀ z ∈ U, ¬ ∀ᶠ y in 𝓝 z, g y = 0 := by
    have hdisj : Disjoint {z : V n | ∀ᶠ y in 𝓝 z, g y = 0} (closure {z : V n | ∀ᶠ y in 𝓝 z, g y = 0})ᶜ :=
      Set.disjoint_left.mpr fun a ha hb => hb (subset_closure ha)
    have hcover : U ⊆ {z : V n | ∀ᶠ y in 𝓝 z, g y = 0} ∪ (closure {z : V n | ∀ᶠ y in 𝓝 z, g y = 0})ᶜ := by
      intro z hz
      by_cases hc : z ∈ closure {z : V n | ∀ᶠ y in 𝓝 z, g y = 0}
      · exact Or.inl (hclosed z hz hc)
      · exact Or.inr hc
    rcases hUc.subset_or_subset hWopen isClosed_closure.isOpen_compl hdisj hcover with h | h
    · obtain ⟨z1, hz1U, hz1⟩ := hg0
      exact absurd (Filter.Eventually.self_of_nhds (h hz1U)) hz1
    · intro z hz hev
      exact h hz (subset_closure hev)
  apply measure_null_of_locally_null
  intro z hz
  obtain ⟨hzU, hgz⟩ := hz
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hzU
  have hex : ∃ z0 ∈ ball z (r / 4), g z0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hWempty z hzU (Metric.eventually_nhds_iff_ball.mpr ⟨r / 4, by linarith, h⟩)
  obtain ⟨z0, hz0, hgz0⟩ := hex
  rw [Metric.mem_ball] at hz0
  have hball : ball z0 (3 * r / 4) ⊆ U := by
    intro y hy
    apply hrU
    rw [Metric.mem_ball] at hy ⊢
    linarith [dist_triangle y z0 z]
  have hnull := volume_ball_inter_zeroSet_eq_zero_of_ne_zero hg (R := 3 * r / 4) (R' := r / 2) (by linarith) (by linarith) hball hgz0
  refine ⟨(U ∩ {z | g z = 0}) ∩ ball z0 (r / 2), inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds ?_), ?_⟩
  · rw [Metric.mem_ball, dist_comm]
    linarith
  · refine measure_mono_null ?_ hnull
    intro y hy
    exact ⟨hy.2, hy.1.2⟩

theorem eq_across {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {f : V n → ℂ} (hf : ContinuousOn f U)
    (h0 : ∀ z ∈ U, g z ≠ 0 → f z = 0) : ∀ z ∈ U, f z = 0 := by
  intro z hz
  by_contra hfz
  have hnull := zero_null hU hUc hg hg0
  have hev : ∀ᶠ y in 𝓝 z, y ∈ U ∧ f y ≠ 0 :=
    Filter.Eventually.and (hU.mem_nhds hz : ∀ᶠ y in 𝓝 z, y ∈ U)
      ((hf.continuousAt (hU.mem_nhds hz)).eventually_ne hfz)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : ball z ε ⊆ U ∩ {y | g y = 0} := fun y hy => by
    obtain ⟨hyU, hfy⟩ := hball y hy
    refine ⟨hyU, ?_⟩
    by_contra hgy
    exact hfy (h0 y hyU hgy)
  exact (Metric.measure_ball_pos volume z hε).ne' (measure_mono_null hsub hnull)

theorem loc_int {U U' : Set (V n)} (hU : IsOpen U) (hU'o : IsOpen U') {g : V n → ℂ}
    (hU' : ∀ y, y ∈ U' ↔ y ∈ U ∧ g y ≠ 0) {H : V n → ℂ} (hH : ContinuousOn H U')
    {ω : V n → ℝ} (hω : ∀ K ⊆ U, IsCompact K → ∃ c > 0, ∀ y ∈ K ∩ U', c ≤ ω y)
    (hI : ∫⁻ y in U', ENNReal.ofReal (‖H y‖ ^ 2 * ω y) < ⊤) :
    ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧ IntegrableOn (fun y => ‖H y‖ ^ 2) (ball z r \ {y | g y = 0}) := by
  intro z hz
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  have hK : closedBall z (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨c, hc, hcω⟩ := hω _ hK (isCompact_closedBall z (ε / 2))
  refine ⟨ε / 2, by linarith, ball_subset_closedBall.trans hK, ?_⟩
  have hS : ball z (ε / 2) \ {y | g y = 0} = ball z (ε / 2) ∩ U' := by
    ext y
    simp only [mem_diff, mem_inter_iff, mem_setOf_eq, hU']
    constructor
    · rintro ⟨hy, hgy⟩
      exact ⟨hy, hK (ball_subset_closedBall hy), hgy⟩
    · rintro ⟨hy, -, hgy⟩
      exact ⟨hy, hgy⟩
  rw [hS]
  have hSo : IsOpen (ball z (ε / 2) ∩ U') := isOpen_ball.inter hU'o
  have hSU : ball z (ε / 2) ∩ U' ⊆ U' := inter_subset_right
  have hcont : ContinuousOn (fun y => ‖H y‖ ^ 2) (ball z (ε / 2) ∩ U') :=
    ((hH.mono hSU).norm).pow 2
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (‖H y‖ ^ 2))
      (volume.restrict (ball z (ε / 2) ∩ U')) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable hSo.measurableSet
  have hbound : ∫⁻ y in ball z (ε / 2) ∩ U', ENNReal.ofReal (‖H y‖ ^ 2) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top : ENNReal.ofReal c⁻¹ < ⊤) hI))
    calc ∫⁻ y in ball z (ε / 2) ∩ U', ENNReal.ofReal (‖H y‖ ^ 2)
        ≤ ∫⁻ y in ball z (ε / 2) ∩ U', ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖H y‖ ^ 2 * ω y) := by
          refine setLIntegral_mono' hSo.measurableSet fun y hy => ?_
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hcy : c ≤ ω y := hcω y ⟨ball_subset_closedBall hy.1, hy.2⟩
          have h1 : 1 ≤ c⁻¹ * ω y := by
            rw [inv_mul_eq_div, one_le_div hc]
            exact hcy
          nlinarith [mul_nonneg (sq_nonneg ‖H y‖) (sub_nonneg.2 h1)]
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ y in ball z (ε / 2) ∩ U', ENNReal.ofReal (‖H y‖ ^ 2 * ω y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c⁻¹ * ∫⁻ y in U', ENNReal.ofReal (‖H y‖ ^ 2 * ω y) :=
          by gcongr
  refine (integrable_toReal_of_lintegral_ne_top hmeas hbound).congr (ae_of_all _ fun y => ?_)
  exact ENNReal.toReal_ofReal (sq_nonneg _)

end UpDivF

end ReciprocityTheory.ChartRestriction.G.AR.Up
