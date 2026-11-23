import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic

namespace PositivityTheory.UnitarySelfGeneration

open Metric Filter Topology Set

namespace GMon

variable {e : ℕ}

theorem update_mem {r : ℝ} {z : Fin e → ℂ} (hz : z ∈ ball (0 : Fin e → ℂ) r) (i : Fin e) {t : ℂ}
    (ht : ‖t‖ < r) : Function.update z i t ∈ ball (0 : Fin e → ℂ) r := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) ht
  rw [mem_ball_zero_iff, pi_norm_lt_iff hr] at hz ⊢
  intro j
  by_cases h : j = i
  · subst h; simpa using ht
  · simpa [Function.update_of_ne h] using hz j

theorem analyticAt_update_left (i : Fin e) (t : ℂ) (z : Fin e → ℂ) :
    AnalyticAt ℂ (fun w : Fin e → ℂ => Function.update w i t) z := by
  refine analyticAt_pi_iff.mpr fun j => ?_
  by_cases h : j = i
  · subst h; simpa using analyticAt_const
  · simp only [Function.update_of_ne h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) j).analyticAt z

theorem analyticAt_update_right (i : Fin e) (z : Fin e → ℂ) (t : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => Function.update z i s) t := by
  refine analyticAt_pi_iff.mpr fun j => ?_
  by_cases h : j = i
  · subst h; simp only [Function.update_self]; exact analyticAt_id
  · simp only [Function.update_of_ne h]
    exact analyticAt_const

theorem norm_sub_update (z : Fin e → ℂ) (i : Fin e) : ‖z - Function.update z i 0‖ ≤ ‖z i‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem isBigO_coord {G : (Fin e → ℂ) → ℂ} {b : Fin e → ℂ} (i : Fin e) (hG : AnalyticAt ℂ G b) (hb : b i = 0)
    (h0 : ∀ᶠ z in 𝓝 b, z i = 0 → G z = 0) : ∃ C : ℝ, ∀ᶠ z in 𝓝 b, ‖G z‖ ≤ C * ‖z i‖ := by
  obtain ⟨C, t, ht, hL⟩ := (hG.contDiffAt (n := 1)).exists_lipschitzOnWith
  have hu : Tendsto (fun w : Fin e → ℂ => Function.update w i 0) (𝓝 b) (𝓝 b) := by
    have := (analyticAt_update_left i 0 b).continuousAt
    rw [ContinuousAt] at this
    rwa [← hb, Function.update_eq_self, hb] at this
  refine ⟨C, ?_⟩
  filter_upwards [ht, hu.eventually ht, hu.eventually h0] with z h1 h2 h3
  have h4 := hL.norm_sub_le h1 h2
  rw [h3 (by simp), sub_zero] at h4
  exact h4.trans (mul_le_mul_of_nonneg_left (norm_sub_update z i) C.2)

theorem divide {G : (Fin e → ℂ) → ℂ} {r : ℝ} (i : Fin e) (hG : AnalyticOnNhd ℂ G (ball 0 r))
    (h0 : ∀ z ∈ ball (0 : Fin e → ℂ) r, z i = 0 → G z = 0) :
    ∃ G' : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ G' (ball 0 r) ∧ ∀ z ∈ ball (0 : Fin e → ℂ) r, G z = z i * G' z := by
  have hi : Differentiable ℂ (fun z : Fin e → ℂ => z i) := by fun_prop
  obtain ⟨F, hF, hE⟩ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.proof e (ball 0 r)
    (fun z => z i) (fun z => G z / z i) isOpen_ball hi.differentiableOn
    (by
      rintro V hV - ⟨z, hz⟩
      have hd : Dense ((fun z : Fin e → ℂ => z i) ⁻¹' ({0}ᶜ)) :=
        (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)
      obtain ⟨w, hw1, hw2⟩ := hd.inter_open_nonempty V hV ⟨z, hz⟩
      exact ⟨w, hw1, hw2⟩)
    (fun z hz => ((hG z hz.1).div ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt z)
      hz.2).differentiableAt.differentiableWithinAt)
    (by
      intro τ hτ
      by_cases hτi : τ i = 0
      · obtain ⟨C, hC⟩ := isBigO_coord i (hG τ hτ) hτi
          (by filter_upwards [isOpen_ball.mem_nhds hτ] with z hz using h0 z hz)
        refine ⟨_, hC, (isBounded_closedBall (x := (0 : ℂ)) (r := C)).subset ?_⟩
        rintro _ ⟨z, ⟨⟨h1, -⟩, h2⟩, rfl⟩
        have h3 : 0 < ‖z i‖ := norm_pos_iff.mpr h2
        simp only [mem_closedBall, dist_zero_right, norm_div]
        rw [div_le_iff₀ h3]
        exact h1
      · have hc : ContinuousAt (fun z => G z / z i) τ :=
          (hG τ hτ).continuousAt.div hi.continuous.continuousAt hτi
        refine ⟨_, hc (ball_mem_nhds _ one_pos), (isBounded_ball (x := G τ / τ i) (r := 1)).subset ?_⟩
        rintro _ ⟨z, ⟨⟨h1, -⟩, -⟩, rfl⟩
        exact h1)
  refine ⟨F, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn
    isOpen_ball hF, fun z hz => ?_⟩
  by_cases hzi : z i = 0
  · rw [h0 z hz hzi, hzi, zero_mul]
  · rw [hE ⟨hz, hzi⟩]
    field_simp

theorem spread {G : (Fin e → ℂ) → ℂ} {r : ℝ} (S : Finset (Fin e)) (i : Fin e) (hG : AnalyticOnNhd ℂ G (ball 0 r))
    (hne : ∀ z ∈ ball (0 : Fin e → ℂ) r, z i ≠ 0 → (∀ j ∈ S, j ≠ i → z j ≠ 0) → G z ≠ 0)
    {b : Fin e → ℂ} (hb : b ∈ ball (0 : Fin e → ℂ) r) (hbS : ∀ j ∈ S, j ≠ i → b j ≠ 0) (hb0 : G b = 0) :
    ∀ z ∈ ball (0 : Fin e → ℂ) r, z i = 0 → G z = 0 := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hb
  have hbi : b i = 0 := by
    by_contra h
    exact hne b hb h hbS hb0
  set ρ : ℝ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r := by linarith

  have hcont : ∀ t ∈ sphere (0 : ℂ) ρ,
      ContinuousAt (fun p : (Fin e → ℂ) × ℂ => G (Function.update p.1 i p.2)) (b, t) := by
    intro t ht
    have h1 : ‖t‖ < r := by rw [mem_sphere_zero_iff_norm.mp ht]; exact hρr
    refine ContinuousAt.comp (hG _ (update_mem hb i h1)).continuousAt ?_
    exact (continuous_fst.update i continuous_snd).continuousAt
  have hpos : ∀ t ∈ sphere (0 : ℂ) ρ, G (Function.update b i t) ≠ 0 := by
    intro t ht
    have h0 : ‖t‖ = ρ := mem_sphere_zero_iff_norm.mp ht
    refine hne _ (update_mem hb i (h0 ▸ hρr)) ?_ fun j hj hji => ?_
    · simp only [Function.update_self]
      rintro rfl
      simp at h0
      linarith
    · rw [Function.update_of_ne hji]; exact hbS j hj hji
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_isMinOn
    (f := fun t => ‖G (Function.update b i t)‖) (NormedSpace.sphere_nonempty.mpr hρ0.le)
    (fun t ht => ((hcont t ht).comp (f := fun t => (b, t))
      (by fun_prop)).norm.continuousWithinAt)
  set δ : ℝ := ‖G (Function.update b i t₀)‖ / 2 with hδ
  have hδ0 : 0 < δ := half_pos (norm_pos_iff.mpr (hpos t₀ ht₀))
  have hev : ∀ᶠ w in 𝓝 b, ∀ t ∈ sphere (0 : ℂ) ρ, δ < ‖G (Function.update w i t)‖ := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun t ht => ?_
    refine (hcont t ht).norm.eventually (lt_mem_nhds ?_)
    have : ‖G (Function.update b i t₀)‖ ≤ ‖G (Function.update b i t)‖ := hmin ht
    simp only
    linarith
  have hU := analyticAt_update_left i 0 b
  have hbb : Function.update b i 0 = b := by rw [← hbi, Function.update_eq_self]
  have hsmall : ∀ᶠ w in 𝓝 b, ‖G (Function.update w i 0)‖ < δ := by
    have : ContinuousAt (fun w => G (Function.update w i 0)) b :=
      ContinuousAt.comp (by rw [hbb]; exact (hG b hb).continuousAt) hU.continuousAt
    refine this.norm.eventually (gt_mem_nhds ?_)
    simp only [hbb, hb0, norm_zero]
    exact hδ0
  have hSev : ∀ᶠ w in 𝓝 b, ∀ j ∈ S, j ≠ i → w j ≠ 0 := by
    refine (S.eventually_all).mpr fun j hj => ?_
    by_cases hji : j = i
    · exact Eventually.of_forall fun w h => absurd hji h
    · filter_upwards [(continuous_apply j).continuousAt.eventually_ne (hbS j hj hji)] with w hw _ using hw
  have hzero : ∀ᶠ w in 𝓝 b, G (Function.update w i 0) = 0 := by
    filter_upwards [hev, hsmall, hSev, isOpen_ball.mem_nhds hb] with w h1 h2 h3 h4
    by_contra hw
    have hnz : ∀ t ∈ closedBall (0 : ℂ) ρ, G (Function.update w i t) ≠ 0 := by
      intro t ht
      by_cases ht0 : t = 0
      · rw [ht0]; exact hw
      · refine hne _ (update_mem h4 i (lt_of_le_of_lt (mem_closedBall_zero_iff.mp ht) hρr))
          (by simpa using ht0) fun j hj hji => ?_
        rw [Function.update_of_ne hji]; exact h3 j hj hji
    have hd : DifferentiableOn ℂ (fun t => (G (Function.update w i t))⁻¹) (closedBall (0 : ℂ) ρ) := by
      intro t ht
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.inv ?_ (hnz t ht))
      exact (AnalyticAt.comp (hG _ (update_mem h4 i (lt_of_le_of_lt (mem_closedBall_zero_iff.mp ht) hρr)))
        (analyticAt_update_right i w t)).differentiableAt
    have hdc : DiffContOnCl ℂ (fun t => (G (Function.update w i t))⁻¹) (ball (0 : ℂ) ρ) := by
      apply DifferentiableOn.diffContOnCl
      rwa [closure_ball _ hρ0.ne']
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc (C := δ⁻¹)
      (fun t ht => by
        rw [frontier_ball _ hρ0.ne'] at ht
        rw [norm_inv]
        exact inv_anti₀ hδ0 (h1 t ht).le) (z := 0) (subset_closure (mem_ball_self hρ0))
    rw [norm_inv] at hle
    have := inv_strictAnti₀ (norm_pos_iff.mpr hw) h2
    linarith
  have han : AnalyticOnNhd ℂ (fun w => G (Function.update w i 0)) (ball 0 r) := fun w hw =>
    AnalyticAt.comp (hG _ (update_mem hw i (by simpa using hr))) (analyticAt_update_left i 0 w)
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hb hzero
  intro z hz hzi
  have := hall hz
  simp only [Pi.zero_apply] at this
  rwa [show Function.update z i 0 = z by rw [← hzi, Function.update_eq_self]] at this

theorem step {F : (Fin e → ℂ) → ℂ} {r : ℝ} (hr : 0 < r) (S : Finset (Fin e)) (i : Fin e)
    (hF : AnalyticOnNhd ℂ F (ball 0 r))
    (hne : ∀ z ∈ ball (0 : Fin e → ℂ) r, z i ≠ 0 → (∀ j ∈ S, j ≠ i → z j ≠ 0) → F z ≠ 0) :
    ∃ (k : ℕ) (G : (Fin e → ℂ) → ℂ), AnalyticOnNhd ℂ G (ball 0 r) ∧
      (∀ z ∈ ball (0 : Fin e → ℂ) r, (∀ j ∈ S, j ≠ i → z j ≠ 0) → G z ≠ 0) ∧
      ∀ z ∈ ball (0 : Fin e → ℂ) r, F z = z i ^ k * G z := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ k : ℕ, ∃ G : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ G (ball 0 r) ∧
      ∀ z ∈ ball (0 : Fin e → ℂ) r, F z = z i ^ k * G z := by
    intro k
    induction k with
    | zero => exact ⟨F, hF, fun z _ => by simp⟩
    | succ k ih =>
      obtain ⟨G, hG, hFG⟩ := ih
      have h1 : ∃ b ∈ ball (0 : Fin e → ℂ) r, (∀ j ∈ S, j ≠ i → b j ≠ 0) ∧ G b = 0 := by
        by_contra h
        push Not at h
        obtain ⟨z, hz, hz'⟩ := hcon k G hG h
        exact hz' (hFG z hz)
      obtain ⟨b, hb, hbS, hb0⟩ := h1
      have h2 := spread S i hG (fun z hz hzi hzS hG0 => hne z hz hzi hzS (by rw [hFG z hz, hG0, mul_zero]))
        hb hbS hb0
      obtain ⟨G', hG', hE⟩ := divide i hG h2
      exact ⟨G', hG', fun z hz => by rw [hFG z hz, hE z hz]; ring⟩
  set b : Fin e → ℂ := fun _ => ((r / 2 : ℝ) : ℂ) with hbdef
  have hb : b ∈ ball (0 : Fin e → ℂ) r := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro j
    simp only [hbdef, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    linarith
  have hm : ∀ᶠ t in 𝓝 (0 : ℂ), Function.update b i t ∈ ball (0 : Fin e → ℂ) r := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht using update_mem hb i (mem_ball_zero_iff.mp ht)
  have hφ : AnalyticAt ℂ (fun t => F (Function.update b i t)) 0 :=
    AnalyticAt.comp (hF _ hm.self_of_nhds) (analyticAt_update_right i b 0)
  have htop : analyticOrderAt (fun t => F (Function.update b i t)) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.mpr fun k => ?_
    obtain ⟨G, hG, hFG⟩ := hall k
    refine (natCast_le_analyticOrderAt hφ).mpr ⟨fun t => G (Function.update b i t),
      AnalyticAt.comp (hG _ hm.self_of_nhds) (analyticAt_update_right i b 0), ?_⟩
    filter_upwards [hm] with t ht
    rw [hFG _ ht]
    simp
  rw [analyticOrderAt_eq_top] at htop
  have h3 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), False := by
    filter_upwards [nhdsWithin_le_nhds htop, nhdsWithin_le_nhds hm, self_mem_nhdsWithin] with t h1 h2 h3
    refine hne _ h2 (by simpa using h3) (fun j _ hji => ?_) h1
    rw [Function.update_of_ne hji]
    simp only [hbdef]
    exact_mod_cast (half_pos hr).ne'
  obtain ⟨_, h⟩ := h3.exists
  exact h

end GMon

theorem g_monomial : ∀ (e : ℕ) (S : Finset (Fin e)) (F : (Fin e → ℂ) → ℂ) (r : ℝ), 0 < r → AnalyticOnNhd ℂ F (Metric.ball 0 r) → (∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, (∀ i ∈ S, z i ≠ 0) → F z ≠ 0) → ∃ (m : Fin e → ℕ) (u : (Fin e → ℂ) → ℂ), (∀ i, i ∉ S → m i = 0) ∧ AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧ (∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, u z ≠ 0) ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, F z = u z * ∏ i, z i ^ m i := by
  intro e S F r hr
  induction S using Finset.induction_on generalizing F with
  | empty =>
    intro hF hne
    exact ⟨fun _ => 0, F, fun _ _ => rfl, hF, fun z hz => hne z hz (by simp), fun z _ => by simp⟩
  | insert i S hi ih =>
    intro hF hne
    obtain ⟨k, G, hG, hGne, hFG⟩ := GMon.step hr S i hF fun z hz hzi hzS => hne z hz fun j hj => by
      rcases Finset.mem_insert.mp hj with hj | hj
      · rw [hj]; exact hzi
      · exact hzS j hj fun h => hi (h ▸ hj)
    obtain ⟨m, u, hm, hu, hu0, hE⟩ := ih G hG fun z hz hzS => hGne z hz fun j hj _ => hzS j hj
    refine ⟨m + Pi.single i k, u, fun j hj => ?_, hu, hu0, fun z hz => ?_⟩
    · rw [Finset.mem_insert, not_or] at hj
      simp [hm j hj.2, Pi.single_eq_of_ne hj.1]
    · rw [hFG z hz, hE z hz]
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      have : ∏ j, z j ^ (Pi.single i k : Fin e → ℕ) j = z i ^ k := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · simp
      rw [this]
      ring

end PositivityTheory.UnitarySelfGeneration
