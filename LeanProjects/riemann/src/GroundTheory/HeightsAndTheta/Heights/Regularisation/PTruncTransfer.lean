import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncTransfer
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)

noncomputable section

namespace TruncTransfer

theorem exists_lipschitz_near {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hf : ∀ y ∈ W, ContDiffAt ℝ 1 f y) :
    ∃ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, closedBall z ε ⊆ W ∧
      ∀ y ∈ closedBall z ε, ‖f y - f z‖ ≤ C * ‖y - z‖ := by
  obtain ⟨ε, hε, hεW⟩ := hK.exists_cthickening_subset_open hW hKW
  have hc : IsCompact (cthickening ε K) := hK.cthickening
  have hcont : ContinuousOn (fderiv ℝ f) (cthickening ε K) := fun y hy =>
    ((hf y (hεW hy)).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨ε, hε, max C 0, le_max_right _ _, fun z hz =>
    ⟨(closedBall_subset_cthickening hz ε).trans hεW, fun y hy => ?_⟩⟩
  have hsub := closedBall_subset_cthickening hz ε
  exact (convex_closedBall z ε).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (hf w (hεW (hsub hw))).differentiableAt one_ne_zero)
    (fun w hw => (hC w (hsub hw)).trans (le_max_left _ _)) (mem_closedBall_self hε.le) hy

theorem limsupExt_max_le {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) (S : Finset (Fin D))
    (v : (Fin D → ℂ) → ℝ) (K c r : ℝ) {y : Fin D → ℂ} (hy : y ∈ U) (hr : 0 < r)
    (h : ∀ y' ∈ ball y r, y' ∈ U → y' ∉ coordDiv S → max (v y') (-K) ≤ c) :
    limsupExt U (coordDiv S) (fun y' => max (v y') (-K)) y ≤ c := by
  unfold limsupExt
  split_ifs with hyS
  · have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := S) hU hy
    refine limsup_le_of_le (isCoboundedUnder_le_of_le _ fun _ => le_max_right _ (-K)) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds y hr)] with y' hy' hb
    exact h y' hb hy'.1 hy'.2
  · exact h y (mem_ball_self hr) hy hyS

variable {D : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : FinHolAtlas D X}
  (R : RegChartData A)

theorem isCompact_chart_image (j : Fin R.N) {s : Set X} (hs : s ⊆ closure (R.mid j))
    (hsc : IsClosed s) : IsCompact (R.chart j '' s) :=
  hsc.isCompact.image_of_continuousOn ((R.chart j).continuousOn.mono (hs.trans (R.closure_mid j)))

theorem trunc_bdd (k : Fin R.N) : ∃ c > 0, ∃ M : ℝ, ∀ K : ℝ, ∀ x ∈ R.mid k, ∀ s ≤ c,
    ∀ y ∈ closedBall (R.chart k x) s, R.trunc K k y ≤ max M (-K) := by
  have hKk := isCompact_chart_image R k subset_rfl isClosed_closure
  obtain ⟨ε, hε, hεT⟩ := hKk.exists_cthickening_subset_open (R.chart k).open_target
    (image_subset_iff.2 fun x hx => (R.chart k).map_source (R.closure_mid k hx))
  have hc : IsCompact (cthickening ε (R.chart k '' closure (R.mid k))) := hKk.cthickening
  obtain ⟨Mq, hMq⟩ := hc.exists_bound_of_continuousOn ((R.q_smooth k).continuousOn.mono hεT)
  refine ⟨ε / 2, half_pos hε, Mq + R.Cph, fun K x hx s hs y hy => ?_⟩
  have hxK : R.chart k x ∈ R.chart k '' closure (R.mid k) := mem_image_of_mem _ (subset_closure hx)
  have hball := closedBall_subset_cthickening hxK ε
  have hyε : dist y (R.chart k x) ≤ ε / 2 := (mem_closedBall.1 hy).trans hs
  have hyT : y ∈ (R.chart k).target := hεT (hball (mem_closedBall.2 (by linarith)))
  refine limsupExt_max_le (R.chart k).open_target _ _ K _ _ hyT (half_pos hε)
    fun y' hy' hy'T hy'S => ?_
  have hy'c : y' ∈ cthickening ε (R.chart k '' closure (R.mid k)) :=
    hball (mem_closedBall.2 (by linarith [dist_triangle y' y (R.chart k x), mem_ball.1 hy']))
  have hq : R.q k y' ≤ Mq := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMq y' hy'c)
  have hph := R.ph_le _ (R.symm_mem_Yo k hy'T hy'S)
  refine max_le_max ?_ le_rfl
  show R.q k y' + R.ph ((R.chart k).symm y') ≤ Mq + R.Cph
  linarith

theorem pair (j k : Fin R.N) : ∃ δ₀ > 0, ∃ c₀ > 0, ∃ L₀ B₀ : ℝ, ∀ δ L B : ℝ, δ ≤ δ₀ → L * δ ≤ c₀ →
    2 * L₀ ≤ L → 1 ≤ L → B₀ ≤ B →
    ∀ K : ℝ, ∀ x ∈ R.mid j ∩ R.mid k, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ closedBall (R.chart j x) t,
      R.trunc K j y ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
        (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t := by
  set W := (R.chart j).target ∩ (R.chart j).symm ⁻¹' (R.chart k).source with hW
  have hWo : IsOpen W := (R.chart j).isOpen_inter_preimage_symm (R.chart k).open_source
  obtain ⟨τ, hτ⟩ : ∃ f : (Fin D → ℂ) → (Fin D → ℂ), f = R.chart k ∘ (R.chart j).symm := ⟨_, rfl⟩
  have hτy : ∀ y, τ y = R.chart k ((R.chart j).symm y) := fun y => by rw [hτ]; rfl
  obtain ⟨Δ, hΔ⟩ : ∃ f : (Fin D → ℂ) → ℝ, f = fun y => R.q j y - R.q k (τ y) := ⟨_, rfl⟩
  have hΔy : ∀ y, Δ y = R.q j y - R.q k (τ y) := fun y => by rw [hΔ]
  have hKc : IsCompact (R.chart j '' (closure (R.mid j) ∩ closure (R.mid k))) :=
    isCompact_chart_image R j inter_subset_left (isClosed_closure.inter isClosed_closure)
  have hKW : R.chart j '' (closure (R.mid j) ∩ closure (R.mid k)) ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    have hxj := R.closure_mid j hx.1
    refine ⟨(R.chart j).map_source hxj, ?_⟩
    show (R.chart j).symm (R.chart j x) ∈ (R.chart k).source
    rw [(R.chart j).left_inv hxj]
    exact R.closure_mid k hx.2
  have hτan : ∀ y ∈ W, AnalyticAt ℂ τ y := by
    intro y hy
    have h := analyticAt_transition (R.compat j) (R.compat k) ((R.chart j).map_target hy.1) hy.2
    rw [(R.chart j).right_inv hy.1] at h
    rwa [hτ]
  have hτc : ∀ y ∈ W, ContDiffAt ℝ 1 τ y := fun y hy =>
    (hτan y hy).restrictScalars.contDiffAt
  have hτT : ∀ y ∈ W, τ y ∈ (R.chart k).target := fun y hy => by
    rw [hτy]; exact (R.chart k).map_source hy.2
  have hΔc : ∀ y ∈ W, ContDiffAt ℝ 1 Δ y := by
    intro y hy
    have hqj : ContDiffAt ℝ 1 (R.q j) y :=
      ((R.q_smooth j).contDiffAt ((R.chart j).open_target.mem_nhds hy.1)).of_le (by simp)
    have hqk : ContDiffAt ℝ 1 (R.q k) (τ y) :=
      ((R.q_smooth k).contDiffAt ((R.chart k).open_target.mem_nhds (hτT y hy))).of_le (by simp)
    rw [hΔ]
    exact hqj.sub (hqk.comp y (hτc y hy))
  obtain ⟨ε₁, hε₁, C₁, hC₁, hτL⟩ := exists_lipschitz_near hWo hKc hKW hτc
  obtain ⟨ε₂, hε₂, C₂, hC₂, hΔL⟩ := exists_lipschitz_near hWo hKc hKW hΔc
  obtain ⟨B₀, hB₀⟩ := hKc.exists_bound_of_continuousOn
    (fun y hy => (hΔc y (hKW hy)).continuousAt.continuousWithinAt)
  obtain ⟨c₀, hc₀, Mk, hMk⟩ := trunc_bdd R k
  refine ⟨min ε₁ ε₂ / 2, half_pos (lt_min hε₁ hε₂), c₀, hc₀, max C₁ C₂, B₀, ?_⟩
  intro δ L B hδ hLδ hL₀ hL1 hB K x hx t ht htδ y hy
  have hxj := R.mid_subset_source j hx.1
  have hxk := R.mid_subset_source k hx.2
  have hzK : R.chart j x ∈ R.chart j '' (closure (R.mid j) ∩ closure (R.mid k)) :=
    mem_image_of_mem _ ⟨subset_closure hx.1, subset_closure hx.2⟩
  have hτz : τ (R.chart j x) = R.chart k x := by rw [hτy, (R.chart j).left_inv hxj]
  have hΔz : Δ (R.chart j x) = R.q j (R.chart j x) - R.q k (R.chart k x) := by rw [hΔy, hτz]
  have hΔB : |Δ (R.chart j x)| ≤ B₀ := by simpa [Real.norm_eq_abs] using hB₀ _ hzK
  have hLt : L * t ≤ c₀ := (mul_le_mul_of_nonneg_left htδ.le (by linarith)).trans hLδ
  have hbdd : BddAbove (R.trunc K k '' closedBall (R.chart k x) (L * t)) :=
    ⟨max Mk (-K), by rintro _ ⟨w, hw, rfl⟩; exact hMk K x hx.2 (L * t) hLt w hw⟩
  have h2t : 2 * t ≤ min ε₁ ε₂ := by linarith
  have hCL : max C₁ C₂ * (2 * t) ≤ L * t := by
    have := mul_le_mul_of_nonneg_right hL₀ ht.le
    linarith
  have hC0 : 0 ≤ max C₁ C₂ := hC₁.trans (le_max_left _ _)
  obtain ⟨hWz, hτd⟩ := hτL _ hzK
  have key : ∀ y' ∈ closedBall (R.chart j x) (2 * t), y' ∉ coordDiv (R.S j) →
      max (R.u j y') (-K) ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
        (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t := by
    intro y' hy' hy'S
    have hy'1 : y' ∈ closedBall (R.chart j x) ε₁ :=
      closedBall_subset_closedBall (h2t.trans (min_le_left _ _)) hy'
    have hy'2 : y' ∈ closedBall (R.chart j x) ε₂ :=
      closedBall_subset_closedBall (h2t.trans (min_le_right _ _)) hy'
    have hy'W : y' ∈ W := hWz hy'1
    have hnorm : ‖y' - R.chart j x‖ ≤ 2 * t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy'
    have hx'k : (R.chart j).symm y' ∈ (R.chart k).source := hy'W.2
    have hx'Yo : (R.chart j).symm y' ∈ R.Yo := R.symm_mem_Yo j hy'W.1 hy'S
    have hτS : τ y' ∉ coordDiv (R.S k) := by
      rw [hτy]; exact (R.mem_Yo k _ hx'k).1 hx'Yo
    have hu : R.u j y' = R.u k (τ y') + Δ y' := by
      simp only [RegChartData.u, PotentialCharts.chartFun]
      rw [hΔy, hτy, (R.chart k).left_inv hx'k]
      ring
    have htr : R.trunc K k (τ y') = max (R.u k (τ y')) (-K) := by
      rw [RegChartData.trunc, limsupExt, if_neg hτS]
    have hmem : τ y' ∈ closedBall (R.chart k x) (L * t) := by
      rw [mem_closedBall, dist_eq_norm, ← hτz]
      calc ‖τ y' - τ (R.chart j x)‖ ≤ C₁ * ‖y' - R.chart j x‖ := hτd y' hy'1
        _ ≤ max C₁ C₂ * (2 * t) :=
          mul_le_mul (le_max_left _ _) hnorm (norm_nonneg _) hC0
        _ ≤ L * t := hCL
    have hP : R.u k (τ y') ≤ polyMax (R.trunc K k) (R.chart k x) (L * t) :=
      calc R.u k (τ y') ≤ max (R.u k (τ y')) (-K) := le_max_left _ _
        _ = R.trunc K k (τ y') := htr.symm
        _ ≤ polyMax (R.trunc K k) (R.chart k x) (L * t) := le_csSup hbdd (mem_image_of_mem _ hmem)
    have hΔle : Δ y' ≤ Δ (R.chart j x) + L * t := by
      have h1 := (hΔL _ hzK).2 y' hy'2
      rw [Real.norm_eq_abs] at h1
      have h2 : C₂ * ‖y' - R.chart j x‖ ≤ max C₁ C₂ * (2 * t) :=
        mul_le_mul (le_max_right _ _) hnorm (norm_nonneg _) hC0
      linarith [le_abs_self (Δ y' - Δ (R.chart j x))]
    have hm1 := le_max_left (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B)
    have hm2 := le_max_right (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B)
    have hΔa := abs_le.1 hΔB
    have hLt0 : 0 ≤ L * t := mul_nonneg (by linarith) ht.le
    rw [hu]
    refine max_le ?_ ?_ <;> linarith
  have hyW : y ∈ W := hWz (closedBall_subset_closedBall
    (by linarith [min_le_left ε₁ ε₂] : t ≤ ε₁) hy)
  exact limsupExt_max_le (R.chart j).open_target _ _ K _ _ hyW.1 ht fun y' hy' _ hy'S =>
    key y' (mem_closedBall.2 (by
      linarith [dist_triangle y' y (R.chart j x), mem_ball.1 hy', mem_closedBall.1 hy])) hy'S

end TruncTransfer

theorem TruncTransfer.proof : TruncTransfer.Statement := by
  intro X _ _ _ D A R
  choose δ₀ hδ₀ c₀ hc₀ L₀ B₀ hP using fun j k => TruncTransfer.pair R j k
  obtain ⟨L', hL'⟩ := (Set.finite_range (fun p : Fin R.N × Fin R.N => L₀ p.1 p.2)).bddAbove
  obtain ⟨B, hB⟩ := (Set.finite_range (fun p : Fin R.N × Fin R.N => B₀ p.1 p.2)).bddAbove
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = max 1 (2 * L') := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := (Set.finite_range
    (fun p : Fin R.N × Fin R.N => max (δ₀ p.1 p.2)⁻¹ (L / c₀ p.1 p.2))).bddAbove
  have hm1 : 0 < max m 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max m 1)⁻¹, L, B, inv_pos.2 hm1, hL ▸ le_max_left _ _,
    fun K j k x hx t ht htδ y hy => ?_⟩
  have hmj : max (δ₀ j k)⁻¹ (L / c₀ j k) ≤ max m 1 :=
    (hm (Set.mem_range_self (j, k)) : _).trans (le_max_left _ _)
  refine hP j k (max m 1)⁻¹ L B ?_ ?_ ?_ (hL ▸ le_max_left _ _)
    (hB (Set.mem_range_self (j, k))) K x hx t ht htδ y hy
  · exact inv_le_of_inv_le₀ (hδ₀ j k) ((le_max_left _ _).trans hmj)
  · have h1 : L / c₀ j k ≤ max m 1 := (le_max_right _ _).trans hmj
    rw [div_le_iff₀ (hc₀ j k)] at h1
    rw [← div_eq_mul_inv, div_le_iff₀ hm1]
    linarith [mul_comm (max m 1) (c₀ j k)]
  · have h2 : L₀ j k ≤ L' := hL' (Set.mem_range_self (j, k))
    rw [hL]
    exact le_trans (by linarith) (le_max_right _ _)

end

end GroundTheory.Heights₂.Heights.Regular
