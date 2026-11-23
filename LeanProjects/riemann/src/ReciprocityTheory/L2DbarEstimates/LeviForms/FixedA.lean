import ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_wd_eq_fderiv {n : ℕ} (j : Fin n) (h : V n → ℂ) (y : V n)
    (hy : DifferentiableAt ℂ h y) : wd n j h y = fderiv ℂ h y (bas n j) := by
  unfold wd
  rw [hy.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination (-(fderiv ℂ h y (bas n j)) / 2) * Complex.I_sq

private lemma deriv_comp_line_zero_eq_fderiv {n : ℕ} (h : V n → ℂ) (x w : V n) (hd : DifferentiableAt ℂ h x) :
    deriv (fun t : ℂ => h (x + t • w)) 0 = fderiv ℂ h x w := by
  have h1 : HasDerivAt (fun t : ℂ => x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add x
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 h1 (by simp)).deriv

private lemma norm_fderiv_apply_le_of_bound_on_closedBall {n : ℕ} (h : V n → ℂ) (U : Set (V n)) (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (y : V n) (R M : ℝ) (hR : 0 < R)
    (hsub : closedBall y (6 * R) ⊆ U) (hM : ∀ x ∈ closedBall y (6 * R), ‖h x‖ ≤ M) :
    ∀ x ∈ closedBall y (5 * R), ∀ w : V n, ‖fderiv ℂ h x w‖ ≤ M / R * ‖w‖ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM y (mem_closedBall_self (by positivity)))
  have hmaps : ∀ x ∈ closedBall y (5 * R), ∀ w : V n, ‖w‖ ≤ 1 → ∀ t ∈ closedBall (0 : ℂ) R,
      x + t • w ∈ closedBall y (6 * R) := by
    intro x hx w hw t ht
    rw [mem_closedBall] at hx ht ⊢
    rw [dist_zero_right] at ht
    have h1 : ‖t • w‖ ≤ R := by
      rw [norm_smul]
      nlinarith [norm_nonneg t, norm_nonneg w]
    calc dist (x + t • w) y ≤ dist x y + ‖t • w‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ ≤ 6 * R := by linarith
  have hest1 : ∀ x ∈ closedBall y (5 * R), ∀ w : V n, ‖w‖ ≤ 1 → ‖fderiv ℂ h x w‖ ≤ M / R := by
    intro x hx w hw
    have hxU : x ∈ U := hsub (closedBall_subset_closedBall (by linarith) hx)
    rw [← deriv_comp_line_zero_eq_fderiv h x w (hh.differentiableAt (hU.mem_nhds hxU))]
    have hfd : DifferentiableOn ℂ (fun t : ℂ => h (x + t • w)) (closedBall 0 R) := by
      intro t ht
      have hd : DifferentiableAt ℂ h (x + t • w) :=
        hh.differentiableAt (hU.mem_nhds (hsub (hmaps x hx w hw t ht)))
      exact (hd.comp t ((differentiableAt_const x).add
        (differentiableAt_id.smul_const w))).differentiableWithinAt
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR (hfd.diffContOnCl_ball subset_rfl)
    intro t ht
    exact hM _ (hmaps x hx w hw t (sphere_subset_closedBall ht))
  intro x hx w
  by_cases hw : w = 0
  · rw [hw, map_zero, norm_zero, norm_zero, mul_zero]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwne : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
  set u : V n := ((‖w‖ : ℝ) : ℂ)⁻¹ • w with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos,
      inv_mul_cancel₀ hwpos.ne']
  have hwu : fderiv ℂ h x w = ((‖w‖ : ℝ) : ℂ) * fderiv ℂ h x u := by
    rw [hu, map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hwne, one_mul]
  have h1 := hest1 x hx u hun.le
  rw [hwu, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos]
  nlinarith

private lemma norm_sub_translate_le_of_fderiv_bound {n : ℕ} (h : V n → ℂ) (U : Set (V n)) (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (y : V n) (R M : ℝ) (hR : 0 < R)
    (hsub : closedBall y (5 * R) ⊆ U)
    (hest : ∀ x ∈ closedBall y (5 * R), ∀ w : V n, ‖fderiv ℂ h x w‖ ≤ M / R * ‖w‖)
    (pv : V n) (hpvn : ‖pv‖ ≤ R) :
    ∀ a ∈ ball y R, ∀ b ∈ ball y R, ‖h (a + pv) - h (b + pv)‖ ≤ M / R * ‖a - b‖ := by
  intro a ha b hb
  have hpt : ∀ s ∈ closedBall (0 : ℂ) 1, b + s • (a - b) + pv ∈ closedBall y (5 * R) := by
    intro s hs
    rw [mem_closedBall, dist_zero_right] at hs
    rw [mem_ball] at ha hb
    rw [mem_closedBall]
    have hab : ‖a - b‖ ≤ 2 * R := by
      calc ‖a - b‖ = ‖(a - y) - (b - y)‖ := by congr 1; abel
        _ ≤ ‖a - y‖ + ‖b - y‖ := norm_sub_le _ _
        _ ≤ 2 * R := by rw [← dist_eq_norm, ← dist_eq_norm]; linarith
    have hs2 : ‖s • (a - b)‖ ≤ 2 * R := by
      rw [norm_smul]
      nlinarith [norm_nonneg s, norm_nonneg (a - b)]
    calc dist (b + s • (a - b) + pv) y = ‖(b - y) + s • (a - b) + pv‖ := by
          rw [dist_eq_norm]
          congr 1
          abel
      _ ≤ ‖b - y‖ + ‖s • (a - b)‖ + ‖pv‖ := norm_add₃_le
      _ ≤ 5 * R := by rw [← dist_eq_norm]; linarith
  have hdv : ∀ s ∈ closedBall (0 : ℂ) 1, HasDerivAt (fun s : ℂ => h (b + s • (a - b) + pv))
      (fderiv ℂ h (b + s • (a - b) + pv) (a - b)) s := by
    intro s hs
    have hd := (hh.differentiableAt (hU.mem_nhds (hsub (hpt s hs)))).hasFDerivAt
    have h1 : HasDerivAt (fun s : ℂ => b + s • (a - b) + pv) (a - b) s := by
      simpa using (((hasDerivAt_id s).smul_const (a - b)).const_add b).add_const pv
    exact hd.comp_hasDerivAt s h1
  have hmvt := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le
    (f := fun s : ℂ => h (b + s • (a - b) + pv)) (C := M / R * ‖a - b‖) (x := 0) (y := 1)
    (fun s hs => (hdv s hs).differentiableAt)
    (fun s hs => by rw [(hdv s hs).deriv]; exact hest _ (hpt s hs) _)
    (mem_closedBall_self zero_le_one) (by simp)
  simpa using hmvt

theorem fx_differentiableOn_wd {n : ℕ} (j : Fin n) (h : V n → ℂ) (U : Set (V n)) (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) : DifferentiableOn ℂ (wd n j h) U := by
  classical
  set v : V n := bas n j with hvdef
  have hvn : ‖v‖ = 1 := by
    rw [hvdef]
    unfold bas
    rw [EuclideanSpace.norm_single, norm_one]
  have hwd_eq : ∀ y ∈ U, wd n j h y = fderiv ℂ h y v :=
    fun y hy => fx_wd_eq_fderiv j h y (hh.differentiableAt (hU.mem_nhds hy))
  suffices H : ∀ y ∈ U, DifferentiableAt ℂ (fun y' => fderiv ℂ h y' v) y by
    intro y hy
    refine ((H y hy).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hU.mem_nhds hy] with y' hy'
    exact hwd_eq y' hy'
  intro y hy
  obtain ⟨R0, hR0, hball⟩ := Metric.isOpen_iff.mp hU y hy
  obtain ⟨R, hR, hRdef⟩ : ∃ R : ℝ, 0 < R ∧ R = R0 / 8 := ⟨R0 / 8, by positivity, rfl⟩
  have hR0' : 0 ≤ R := hR.le
  have hsub : closedBall y (6 * R) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hsub5 : closedBall y (5 * R) ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hsub
  obtain ⟨M, hM⟩ := (isCompact_closedBall y (6 * R)).exists_bound_of_continuousOn
    (hh.continuousOn.mono hsub)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM y (mem_closedBall_self (by positivity)))
  have hest := norm_fderiv_apply_le_of_bound_on_closedBall h U hU hh y R M hR hsub hM
  have hin : ∀ y' ∈ ball y R, ∀ θ : ℝ, y' + circleMap 0 R θ • v ∈ closedBall y (5 * R) := by
    intro y' hy' θ
    rw [mem_ball] at hy'
    rw [mem_closedBall]
    have h1 : ‖circleMap 0 R θ • v‖ = R := by
      rw [norm_smul, norm_circleMap_zero, hvn, mul_one, abs_of_pos hR]
    calc dist (y' + circleMap 0 R θ • v) y ≤ dist y' y + ‖circleMap 0 R θ • v‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ ≤ 5 * R := by linarith
  have hpvn : ∀ θ : ℝ, ‖circleMap 0 R θ • v‖ ≤ R := fun θ => by
    rw [norm_smul, norm_circleMap_zero, hvn, mul_one, abs_of_pos hR]
  have hne : ∀ θ : ℝ, circleMap 0 R θ - 0 ≠ 0 := by
    intro θ h0
    have := norm_circleMap_zero R θ
    rw [sub_zero] at h0
    rw [h0, norm_zero, abs_of_pos hR] at this
    linarith
  have hc1 : ∀ θ : ℝ, ‖circleMap 0 R θ * Complex.I‖ = R := fun θ => by
    rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hR]
  have hc2 : ∀ θ : ℝ, ‖1 / (circleMap 0 R θ - 0) ^ 2‖ = 1 / R ^ 2 := fun θ => by
    rw [norm_div, norm_one, norm_pow, sub_zero, norm_circleMap_zero, abs_of_pos hR]
  have hformula : ∀ y' ∈ ball y R, fderiv ℂ h y' v = (2 * ↑Real.pi * Complex.I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * Real.pi, (circleMap 0 R θ * Complex.I) •
        ((1 / (circleMap 0 R θ - 0) ^ 2) • h (y' + circleMap 0 R θ • v)) := by
    intro y' hy'
    have hy'5 : y' ∈ closedBall y (5 * R) :=
      closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy')
    have hfd : DifferentiableOn ℂ (fun t : ℂ => h (y' + t • v)) (closedBall 0 R) := by
      intro t ht
      have hpt : y' + t • v ∈ closedBall y (5 * R) := by
        rw [mem_closedBall] at ht ⊢
        rw [dist_zero_right] at ht
        rw [mem_ball] at hy'
        have h1 : ‖t • v‖ ≤ R := by rw [norm_smul, hvn, mul_one]; exact ht
        calc dist (y' + t • v) y ≤ dist y' y + ‖t • v‖ := by
              rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
              exact norm_add_le _ _
          _ ≤ 5 * R := by linarith
      have hd : DifferentiableAt ℂ h (y' + t • v) := hh.differentiableAt (hU.mem_nhds (hsub5 hpt))
      exact (hd.comp t ((differentiableAt_const y').add
        (differentiableAt_id.smul_const v))).differentiableWithinAt
    have hc := DifferentiableOn.deriv_eq_smul_circleIntegral hR hfd
    have hci : (∮ z in C(0, R), (1 / (z - 0) ^ 2) • h (y' + z • v)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, (circleMap 0 R θ * Complex.I) •
          ((1 / (circleMap 0 R θ - 0) ^ 2) • h (y' + circleMap 0 R θ • v)) := by
      simp only [circleIntegral, deriv_circleMap]
    rw [← deriv_comp_line_zero_eq_fderiv h y' v (hh.differentiableAt (hU.mem_nhds (hsub5 hy'5))), ← hci, hc,
      inv_smul_smul₀]
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcoef : Continuous (fun θ : ℝ => circleMap 0 R θ * Complex.I) :=
    (continuous_circleMap 0 R).mul continuous_const
  have hcoef2 : Continuous (fun θ : ℝ => 1 / (circleMap 0 R θ - 0) ^ 2) :=
    continuous_const.div (((continuous_circleMap 0 R).sub continuous_const).pow 2)
      fun θ => pow_ne_zero 2 (hne θ)
  have hFc : ∀ y' ∈ ball y R, Continuous (fun θ : ℝ => (circleMap 0 R θ * Complex.I) •
      ((1 / (circleMap 0 R θ - 0) ^ 2) • h (y' + circleMap 0 R θ • v))) := by
    intro y' hy'
    exact hcoef.smul (hcoef2.smul (hh.continuousOn.comp_continuous
      (continuous_const.add ((continuous_circleMap 0 R).smul continuous_const))
      fun θ => hsub5 (hin y' hy' θ)))
  have hbd0 : 0 ≤ R * (1 / R ^ 2) * (M / R) :=
    mul_nonneg (mul_nonneg hR0' (by positivity)) (div_nonneg hM0 hR0')
  have hlip : ∀ θ : ℝ, LipschitzOnWith (Real.nnabs (R * (1 / R ^ 2) * (M / R)))
      (fun y' => (circleMap 0 R θ * Complex.I) •
        ((1 / (circleMap 0 R θ - 0) ^ 2) • h (y' + circleMap 0 R θ • v))) (ball y R) := by
    intro θ
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [Real.coe_nnabs, abs_of_nonneg hbd0, dist_eq_norm, dist_eq_norm]
    simp only [smul_eq_mul]
    rw [← mul_sub, ← mul_sub, norm_mul (circleMap 0 R θ * Complex.I),
      norm_mul (1 / (circleMap 0 R θ - 0) ^ 2), hc1, hc2]
    have hl := norm_sub_translate_le_of_fderiv_bound h U hU hh y R M hR hsub5 hest _ (hpvn θ) a ha b hb
    calc R * (1 / R ^ 2 * ‖h (a + circleMap 0 R θ • v) - h (b + circleMap 0 R θ • v)‖)
        ≤ R * (1 / R ^ 2 * (M / R * ‖a - b‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl (by positivity)) hR0'
      _ = R * (1 / R ^ 2) * (M / R) * ‖a - b‖ := by ring
  have hderivs : ∀ θ : ℝ, HasFDerivAt (fun y' => (circleMap 0 R θ * Complex.I) •
      ((1 / (circleMap 0 R θ - 0) ^ 2) • h (y' + circleMap 0 R θ • v)))
      ((circleMap 0 R θ * Complex.I) •
        ((1 / (circleMap 0 R θ - 0) ^ 2) • fderiv ℂ h (y + circleMap 0 R θ • v))) y := by
    intro θ
    have hpt : y + circleMap 0 R θ • v ∈ U := hsub5 (hin y (mem_ball_self hR) θ)
    have hd : HasFDerivAt h (fderiv ℂ h (y + circleMap 0 R θ • v)) (y + circleMap 0 R θ • v) :=
      (hh.differentiableAt (hU.mem_nhds hpt)).hasFDerivAt
    have h3 : HasFDerivAt (fun y'' => h (y'' + circleMap 0 R θ • v))
        (fderiv ℂ h (y + circleMap 0 R θ • v)) y := by
      have := hd.comp y ((hasFDerivAt_id y).add_const (circleMap 0 R θ • v))
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    exact (h3.const_smul (1 / (circleMap 0 R θ - 0) ^ 2)).const_smul (circleMap 0 R θ * Complex.I)
  have hm : Measurable (fun θ : ℝ => fderiv ℂ h (y + circleMap 0 R θ • v)) :=
    (measurable_fderiv ℂ h).comp
      (continuous_const.add ((continuous_circleMap 0 R).smul continuous_const)).measurable
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * Real.pi)
    (bound := fun _ => R * (1 / R ^ 2) * (M / R))
    (ball_mem_nhds y hR)
    (by
      filter_upwards [ball_mem_nhds y hR] with y' hy'
      exact (hFc y' hy').aestronglyMeasurable)
    ((hFc y (mem_ball_self hR)).intervalIntegrable _ _)
    ((hcoef.aestronglyMeasurable).smul ((hcoef2.aestronglyMeasurable).smul hm.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun θ _ => hlip θ)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => hderivs θ)
  refine (key.2.differentiableAt.const_smul ((2 * ↑Real.pi * Complex.I)⁻¹)).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds y hR] with y' hy'
  exact hformula y' hy'

theorem fx_differentiableOn_jac_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) : DifferentiableOn ℂ (fun y => jac n z g (e.symm y)) e.target := by
  have key : ∀ (f : M → ℂ) (k : Fin n) (y : V n), y ∈ e.target →
      d n z k f (e.symm y) = wd n k (f ∘ e.symm) y := by
    intro f k y hy
    have hx : e.symm y ∈ e.source := e.map_target hy
    have hzx : z (e.symm y) = y := by rw [he hx, e.right_inv hy]
    have hex : ∃ e' : OpenPartialHomeomorph M (V n), IsChart n z e' ∧ e.symm y ∈ e'.source :=
      ⟨e, he, hx⟩
    unfold d
    rw [dif_pos hex, hzx]
    obtain ⟨he', hx'⟩ := Classical.choose_spec hex
    have hev : (f ∘ (Classical.choose hex).symm) =ᶠ[𝓝 y] (f ∘ e.symm) := by
      have h1 : ∀ᶠ w in 𝓝 y, w ∈ e.target := e.open_target.mem_nhds hy
      have h2 : ∀ᶠ w in 𝓝 y, e.symm w ∈ (Classical.choose hex).source :=
        (e.continuousAt_symm hy).preimage_mem_nhds ((Classical.choose hex).open_source.mem_nhds hx')
      filter_upwards [h1, h2] with w hw1 hw2
      simp only [Function.comp]
      congr 1
      have hw : (Classical.choose hex) (e.symm w) = w := by
        rw [← he' hw2, he (e.map_target hw1), e.right_inv hw1]
      calc (Classical.choose hex).symm w
          = (Classical.choose hex).symm ((Classical.choose hex) (e.symm w)) := by rw [hw]
        _ = e.symm w := (Classical.choose hex).left_inv hw2
    unfold wd
    rw [hev.fderiv_eq]
  have hwd : ∀ i k, DifferentiableOn ℂ (wd n k (g i ∘ e.symm)) e.target :=
    fun i k => fx_differentiableOn_wd k _ e.target e.open_target (hg i e he)
  have hform : (fun y => (Matrix.of fun i k => wd n k (g i ∘ e.symm) y).det) =
      fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, wd n i (g (σ i) ∘ e.symm) y := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  have hdet : DifferentiableOn ℂ (fun y => (Matrix.of fun i k => wd n k (g i ∘ e.symm) y).det)
      e.target := by
    rw [hform]
    have hp : ∀ σ : Equiv.Perm (Fin n), DifferentiableOn ℂ
        (fun y => ∏ i, wd n i (g (σ i) ∘ e.symm) y) e.target := by
      intro σ
      have hs : ∀ s : Finset (Fin n), DifferentiableOn ℂ
          (fun y => ∏ i ∈ s, wd n i (g (σ i) ∘ e.symm) y) e.target := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [differentiableOn_const]
        | insert a s ha ih =>
          simp only [Finset.prod_insert ha]
          first
            | exact (hwd (σ a) a).mul ih
            | exact (hwd (σ a) a).fun_mul ih
      exact hs Finset.univ
    have hq : ∀ σ : Equiv.Perm (Fin n), DifferentiableOn ℂ
        (fun y => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, wd n i (g (σ i) ∘ e.symm) y) e.target := by
      intro σ
      first
        | exact (hp σ).const_mul _
        | exact (differentiableOn_const _).fun_mul (hp σ)
        | exact (differentiableOn_const _).mul (hp σ)
    first
      | exact DifferentiableOn.sum fun σ _ => hq σ
      | exact DifferentiableOn.fun_sum fun σ _ => hq σ
  refine hdet.congr fun y hy => ?_
  unfold jac
  congr 1
  ext i k
  simp only [Matrix.of_apply]
  exact key _ _ y hy

theorem fx_continuous_jac {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) :
    Continuous (jac n z g) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hxe, hze⟩ := hz x
  have he : IsChart n z e := fun x' _ => by rw [hze]
  have h1 : ContinuousAt (fun y => jac n z g (e.symm y)) (e x) :=
    ((fx_differentiableOn_jac_chart n z g hg e he).continuousOn).continuousAt
      (e.open_target.mem_nhds (e.map_source hxe))
  have h2 : ContinuousAt (fun x' => jac n z g (e.symm (e x'))) x := h1.comp (e.continuousAt hxe)
  refine h2.congr ?_
  filter_upwards [e.open_source.mem_nhds hxe] with x' hx'
  rw [e.left_inv hx']

theorem fx_continuous_ev {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (hph : SmoothR n z ph) (r : ℝ) : Continuous (ev n g ph r) := by
  have hcont : ∀ f : M → ℂ, (∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      ContinuousOn (f ∘ e.symm) e.target) → Continuous f := by
    intro f hf
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e, hxe, hze⟩ := hz x
    have he : IsChart n z e := fun x' _ => by rw [hze]
    have h1 : ContinuousAt (f ∘ e.symm) (e x) :=
      (hf e he).continuousAt (e.open_target.mem_nhds (e.map_source hxe))
    have h2 : ContinuousAt (fun x' => f (e.symm (e x'))) x := h1.comp (e.continuousAt hxe)
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hxe] with x' hx'
    rw [e.left_inv hx']
  have hgc : ∀ i, Continuous (g i) := fun i => hcont _ fun e he => (hg i e he).continuousOn
  have hphc : Continuous (fun x => (ph x : ℂ)) := hcont _ fun e he => (hph e he).continuousOn
  have hph' : Continuous ph := by
    have e : ph = Complex.re ∘ fun x => (ph x : ℂ) := by
      funext x
      simp
    rw [e]
    exact Complex.continuous_re.comp hphc
  unfold ev
  exact ((continuous_finset_sum _ fun i _ => (hgc i).norm.pow 2).mul
    (Real.continuous_exp.comp hph'.neg)).div_const _

theorem fx_gt_eq_toFinset {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (c : M → ℂ) (W : M → Set M) (hS : (zeroSet n g).Finite) (x : M) :
    gt n z g c W x = ∑ q ∈ hS.toFinset, (W q).indicator (fun y => c q * jac n z g y) x := by
  unfold gt
  exact finsum_mem_eq_finite_toFinset_sum _ hS

theorem fx_gt_eq_of_mem {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ)
    (hS : (zeroSet n g).Finite) (hL : IsLocalData n g ph r W m) (p : M) (hp : p ∈ zeroSet n g)
    (x : M) (hx : x ∈ W p) : gt n z g c W x = c p * jac n z g x := by
  rw [fx_gt_eq_toFinset n z g c W hS x, Finset.sum_eq_single p]
  · rw [Set.indicator_of_mem hx]
  · intro q hq hqp
    have hq' : q ∈ zeroSet n g := (Set.Finite.mem_toFinset hS).mp hq
    have hd := (hL.2 p hp).2.2.2.2 q hq' hqp
    apply Set.indicator_of_notMem
    intro hxq
    exact Set.disjoint_left.mp hd (subset_closure hx) (subset_closure hxq)
  · intro hp'
    exact absurd ((Set.Finite.mem_toFinset hS).mpr hp) hp'

theorem fx_gt_eq_zero {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (c : M → ℂ) (W : M → Set M) (hS : (zeroSet n g).Finite) (x : M)
    (hx : x ∉ ⋃ q ∈ zeroSet n g, closure (W q)) : gt n z g c W x = 0 := by
  rw [fx_gt_eq_toFinset n z g c W hS x]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hq' : q ∈ zeroSet n g := (Set.Finite.mem_toFinset hS).mp hq
  apply Set.indicator_of_notMem
  intro hxq
  exact hx (Set.mem_iUnion₂.mpr ⟨q, hq', subset_closure hxq⟩)

theorem fx_norm_gt_le {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (c : M → ℂ) (W : M → Set M) (hS : (zeroSet n g).Finite) (x : M) :
    ‖gt n z g c W x‖ ≤ ∑ q ∈ hS.toFinset, ‖c q‖ * ‖jac n z g x‖ := by
  rw [fx_gt_eq_toFinset n z g c W hS x]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun q _ => ?_)
  refine le_trans (norm_indicator_le_norm_self _ _) ?_
  exact (norm_mul _ _).le

theorem fx_measurable_gt {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ) (r : ℝ) (c : M → ℂ)
    (W : M → Set M) (m : ℝ) (hS : (zeroSet n g).Finite) (hL : IsLocalData n g ph r W m) :
    Measurable (gt n z g c W) := by
  have hjac := (fx_continuous_jac n z hz g hg).measurable
  have e : gt n z g c W = fun x => ∑ q ∈ hS.toFinset, (W q).indicator (fun y => c q * jac n z g y) x :=
    funext (fx_gt_eq_toFinset n z g c W hS)
  rw [e]
  refine Finset.measurable_sum _ fun q hq => ?_
  have hq' : q ∈ zeroSet n g := (Set.Finite.mem_toFinset hS).mp hq
  exact (measurable_const.mul hjac).indicator ((hL.2 q hq').1.measurableSet)

theorem fx_measurable_cutExt {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ) (hph : SmoothR n z ph) (r : ℝ)
    (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (hχ : IsCutoff χ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (hL : IsLocalData n g ph r W m) :
    Measurable (cutExt n z g ph r c W χ ε) := by
  have hev := fx_continuous_ev n z hz g hg ph hph r
  have hχc : Continuous χ := hχ.1.continuous
  have h1 : Measurable fun x => (χ (ev n g ph r x / ε ^ 2) : ℂ) :=
    (Complex.continuous_ofReal.comp (hχc.comp (hev.div_const _))).measurable
  unfold cutExt
  exact h1.mul (fx_measurable_gt n z hz g hg ph r c W m hS hL)

theorem fx_norm_cutExt_le {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (χ : ℝ → ℝ)
    (hχ : IsCutoff χ) (ε : ℝ) (x : M) :
    ‖cutExt n z g ph r c W χ ε x‖ ≤ ‖gt n z g c W x‖ := by
  unfold cutExt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := hχ.2.2.2.1 (ev n g ph r x / ε ^ 2)
  have habs : |χ (ev n g ph r x / ε ^ 2)| ≤ 1 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
  calc |χ (ev n g ph r x / ε ^ 2)| * ‖gt n z g c W x‖ ≤ 1 * ‖gt n z g c W x‖ :=
        mul_le_mul_of_nonneg_right habs (norm_nonneg _)
    _ = ‖gt n z g c W x‖ := one_mul _

theorem fx_cutExt_eq_of_mem {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ)
    (hχ : IsCutoff χ) (ε : ℝ) (hε : 0 < ε)
    (hS : (zeroSet n g).Finite) (hL : IsLocalData n g ph r W m) (p : M) (hp : p ∈ zeroSet n g)
    (x : M) (hx : x ∈ W p) (hev : ev n g ph r x ≤ ε ^ 2 / 2) :
    cutExt n z g ph r c W χ ε x = c p * jac n z g x := by
  unfold cutExt
  have h12 : ev n g ph r x / ε ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  rw [hχ.2.1 _ h12, Complex.ofReal_one, one_mul, fx_gt_eq_of_mem n z g ph r c W m hS hL p hp x hx]

theorem fx_ev_eq_zero {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (p : M)
    (hp : p ∈ zeroSet n g) : ev n g ph r p = 0 := by
  have hp' : ∀ i, g i p = 0 := hp
  simp [ev, hp']

theorem fx_lintegral_lt_top_of_le_indicator {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [OpensMeasurableSpace M] [T2Space M] (μ : Measure M) [IsFiniteMeasureOnCompacts μ]
    (K : Set M) (hK : IsCompact K) (h : M → ℝ) (hh : Continuous h) (f : M → ℝ≥0∞)
    (hf : ∀ x, f x ≤ K.indicator (fun x => ENNReal.ofReal (h x)) x) : ∫⁻ x, f x ∂μ < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hint : IntegrableOn h K μ := hh.continuousOn.integrableOn_compact hK
  calc ∫⁻ x, f x ∂μ ≤ ∫⁻ x, K.indicator (fun x => ENNReal.ofReal (h x)) x ∂μ := lintegral_mono hf
    _ = ∫⁻ x in K, ENNReal.ofReal (h x) ∂μ := lintegral_indicator hKm _
    _ < ⊤ := by
        first
          | exact hint.lintegral_lt_top
          | exact Integrable.lintegral_lt_top hint

theorem fx_wint_eq_withDensity {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n)
    (ps : M → ℝ) (hps : Measurable ps) (F : M → ℂ) :
    wint n z F ps = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(vol n z).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-ps x))) := by
  unfold wint
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-ps x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hps.neg)
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, Function.comp]
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem fx_otNorm_eq_wint {M : Type*} [MeasurableSpace M] (n : ℕ) (z : M → V n) (ph ph2 : M → ℝ)
    (j : ℕ) (F : M → ℂ) :
    otNorm n z ph ph2 j F = wint n z F (fun x => ph2 x + ((n : ℝ) + j) * ph x) := by
  unfold otNorm wint
  refine lintegral_congr fun x => ?_
  rw [show -ph2 x - ((n : ℝ) + j) * ph x = -(ph2 x + ((n : ℝ) + j) * ph x) by ring]

theorem fx_lintegral_enorm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℂ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ = eLpNorm F 2 μ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), ← ENNReal.rpow_mul]
  norm_num

end

end ReciprocityTheory.L2DbarEstimates.I
