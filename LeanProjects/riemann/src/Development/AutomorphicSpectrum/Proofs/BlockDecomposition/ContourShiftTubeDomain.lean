import Mathlib

open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.EisTube

lemma tubeShift_gauss_integrable (ι : Type) [Fintype ι] :
    Integrable (fun y : ι → ℝ => Real.exp (-(∑ i, y i ^ 2) / 4)) := by
  have h : Integrable (fun y : ι → ℝ => ∏ i, Real.exp (-(1 / 4 : ℝ) * y i ^ 2)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq (by norm_num))
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only []
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  ring

lemma tubeShift_gauss_bound {ι : Type} [Fintype ι] (y v : ι → ℝ) (s T : ℝ) (hs : |s| ≤ T) :
    Real.exp (-(∑ i, (y i + s * v i) ^ 2) / 2) ≤
      Real.exp (T ^ 2 * (∑ i, v i ^ 2) / 2) * Real.exp (-(∑ i, y i ^ 2) / 4) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : (∑ i, y i ^ 2) / 2 - s ^ 2 * ∑ i, v i ^ 2 ≤ ∑ i, (y i + s * v i) ^ 2 := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg (y i + 2 * (s * v i))]
  have h2 : s ^ 2 ≤ T ^ 2 := by
    have := abs_nonneg s
    rw [← sq_abs s]
    exact pow_le_pow_left₀ this hs 2
  have h3 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

theorem tubeShift_differentiableOn_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → α → ℂ)
    (hol : ∀ y, DifferentiableOn ℂ (fun w => F w y) U)
    (meas : ∀ w ∈ U, AEStronglyMeasurable (F w) μ)
    (dom : ∀ w₀ ∈ U, ∀ ρ : ℝ, 0 < ρ → Metric.closedBall w₀ ρ ⊆ U →
      ∃ g : α → ℝ, Integrable g μ ∧ ∀ w ∈ Metric.closedBall w₀ ρ, ∀ y, ‖F w y‖ ≤ g y) :
    DifferentiableOn ℂ (fun w => ∫ y, F w y ∂μ) U := by
  intro w₀ hw₀
  obtain ⟨ρ', hρ', hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hw₀)
  obtain ⟨g, hg, hgb⟩ := dom w₀ hw₀ ρ' hρ' hb
  have hρ : 0 < ρ' / 2 := by positivity
  have hball : Metric.ball w₀ (ρ' / 2) ⊆ U := fun w hw =>
    hb (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hw))
  have hderiv : ∀ w ∈ U, ∀ y, HasDerivAt (fun w => F w y) (deriv (fun w => F w y) w) w :=
    fun w hw y => ((hol y).differentiableAt (hU.mem_nhds hw)).hasDerivAt
  have hseq : Tendsto (fun n : ℕ => (ρ' / 2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ρ' / 2)
  have hpos : ∀ n : ℕ, 0 < (ρ' / 2 : ℝ) * (1 / ((n : ℝ) + 1)) := fun n => by positivity
  let u : ℕ → ℂ := fun n => w₀ + (((ρ' / 2 : ℝ) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ)
  have hu : ∀ n, u n ∈ U := fun n => by
    apply hb
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [u, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith
  have hmeas' : AEStronglyMeasurable (fun y => deriv (fun w => F w y) w₀) μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) y => slope (fun w => F w y) w₀ (u n)) (fun n => ?_)
      (ae_of_all _ fun y => ?_)
    · simp only [slope, vsub_eq_sub]
      exact ((meas _ (hu n)).sub (meas _ hw₀)).const_smul (u n - w₀)⁻¹
    · refine (hasDerivAt_iff_tendsto_slope.1 (hderiv w₀ hw₀ y)).comp
        (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩)
      · have := ((Complex.continuous_ofReal.tendsto 0).comp hseq).const_add w₀
        simpa [u] using this
      · have : (((ρ' / 2 : ℝ) * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (hpos n).ne'
        simpa [u] using this
  have hint : Integrable (F w₀) μ := by
    refine hg.mono' (meas w₀ hw₀) (ae_of_all _ fun y => ?_)
    exact hgb w₀ (Metric.mem_closedBall_self hρ'.le) y
  have hbound : ∀ᵐ y ∂μ, ∀ w ∈ Metric.ball w₀ (ρ' / 2),
      ‖deriv (fun w => F w y) w‖ ≤ g y / (ρ' / 2) := by
    refine ae_of_all _ fun y w hw => ?_
    have hsub : Metric.closedBall w (ρ' / 2) ⊆ Metric.closedBall w₀ ρ' := by
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      have := Metric.mem_ball.1 hw
      linarith [dist_triangle z w w₀]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
      ((hol y).diffContOnCl_ball (hsub.trans hb))
      (fun z hz => hgb z (hsub (Metric.sphere_subset_closedBall hz)) y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ) (F := F)
    (F' := fun w y => deriv (fun w => F w y) w) (x₀ := w₀) (s := Metric.ball w₀ (ρ' / 2))
    (bound := fun y => g y / (ρ' / 2)) (Metric.ball_mem_nhds _ hρ)
    (Filter.eventually_of_mem (hU.mem_nhds hw₀) meas) hint hmeas' hbound (hg.div_const _)
    (ae_of_all _ fun y w hw => hderiv w (hball hw) y)
  exact key.2.differentiableAt.differentiableWithinAt

theorem tubeShift_const_of_periodic (U : Set ℂ) (hU : IsOpen U) (hc : IsPreconnected U)
    (Φ : ℂ → ℂ) (hd : DifferentiableOn ℂ Φ U)
    (hper : ∀ w ∈ U, ∀ s : ℝ, Φ (w + (s : ℂ) * Complex.I) = Φ w)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) : Φ a = Φ b := by
  have hz : U.EqOn (deriv Φ) 0 := by
    intro w hw
    have h1 : HasDerivAt Φ (deriv Φ w) (w + ((0 : ℝ) : ℂ) * Complex.I) := by
      simpa using (hd.differentiableAt (hU.mem_nhds hw)).hasDerivAt
    have h2 : HasDerivAt (fun s : ℝ => w + (s : ℂ) * Complex.I) Complex.I 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_add w
    have h3 := HasDerivAt.scomp (0 : ℝ) h1 h2
    have h4 : HasDerivAt (Φ ∘ fun s : ℝ => w + (s : ℂ) * Complex.I) 0 0 := by
      have : (Φ ∘ fun s : ℝ => w + (s : ℂ) * Complex.I) = fun _ => Φ w :=
        funext fun s => hper w hw s
      rw [this]
      exact hasDerivAt_const _ _
    have := h3.unique h4
    simpa using this
  exact hU.is_const_of_deriv_eq_zero hc hd hz ha hb

theorem tubeShift_local {ι : Type} [Fintype ι] (Ω : Set (ι → ℝ)) (H : (ι → ℂ) → ℂ)
    (hH : DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω})
    (x₀ x₁ : ι → ℝ) (R C : ℝ) (hK : Metric.closedBall x₀ R ⊆ Ω)
    (hC : ∀ x ∈ Metric.closedBall x₀ R, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2))
    (hx : dist x₁ x₀ ≤ R / 2) :
    (∫ y : ι → ℝ, H (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I)) =
      ∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I) := by
  have hR : 0 ≤ R := by linarith [dist_nonneg (x := x₁) (y := x₀)]
  let v : ι → ℝ := fun i => x₁ i - x₀ i
  let F : ℂ → (ι → ℝ) → ℂ := fun w y =>
    H (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I + w * (v i : ℂ))
  let U : Set ℂ := {w | -1 < w.re} ∩ {w | w.re < 2}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hv : ∀ i, |v i| ≤ R / 2 := fun i => by
    have := dist_le_pi_dist x₁ x₀ i
    rw [Real.dist_eq] at this
    exact this.trans hx
  have hmemK : ∀ w ∈ U, (fun i => x₀ i + w.re * v i) ∈ Metric.closedBall x₀ R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_pi_le_iff hR]
    intro i
    rw [Real.dist_eq, add_sub_cancel_left, abs_mul]
    have h1 : |w.re| ≤ 2 := abs_le.2 ⟨by linarith [hw.1.out], hw.2.out.le⟩
    calc |w.re| * |v i| ≤ 2 * (R / 2) := mul_le_mul h1 (hv i) (abs_nonneg _) (by norm_num)
      _ = R := by ring
  have hz : ∀ (w : ℂ) (y : ι → ℝ),
      (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I + w * (v i : ℂ)) =
        fun i => (((x₀ i + w.re * v i : ℝ)) : ℂ) + ((y i + w.im * v i : ℝ) : ℂ) * Complex.I := by
    intro w y
    funext i
    apply Complex.ext <;> simp
  have hT : ∀ w ∈ U, ∀ y : ι → ℝ,
      (fun i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I + w * (v i : ℂ)) ∈
        {z : ι → ℂ | (fun i => (z i).re) ∈ Ω} := by
    intro w hw y
    have h1 := hK (hmemK w hw)
    rw [hz w y]
    simpa using h1
  have hol : ∀ y, DifferentiableOn ℂ (fun w => F w y) U := by
    intro y
    refine DifferentiableOn.comp (g := H)
      (f := fun w i => (x₀ i : ℂ) + (y i : ℂ) * Complex.I + w * (v i : ℂ)) hH ?_
      (fun w hw => hT w hw y)
    exact (differentiable_pi.2 fun i => by fun_prop).differentiableOn
  have hcont : ∀ w ∈ U, Continuous (F w) := by
    intro w hw
    refine hH.continuousOn.comp_continuous ?_ (fun y => hT w hw y)
    exact continuous_pi fun i => by fun_prop
  have hbd : ∀ w ∈ U, ∀ y : ι → ℝ,
      ‖F w y‖ ≤ |C| * Real.exp (-(∑ i, (y i + w.im * v i) ^ 2) / 2) := by
    intro w hw y
    have h1 := hC _ (hmemK w hw) (fun i => y i + w.im * v i)
    have h2 : F w y = H (fun i => (((x₀ i + w.re * v i : ℝ)) : ℂ) +
        ((y i + w.im * v i : ℝ) : ℂ) * Complex.I) := by
      simp only [F]
      rw [hz w y]
    rw [h2]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  have hdiff : DifferentiableOn ℂ (fun w => ∫ y, F w y) U := by
    refine tubeShift_differentiableOn_integral volume U hUo F hol
      (fun w hw => (hcont w hw).aestronglyMeasurable) ?_
    intro w₀ _ ρ _ hb
    refine ⟨fun y => (|C| * Real.exp ((|w₀.im| + ρ) ^ 2 * (∑ i, v i ^ 2) / 2)) *
      Real.exp (-(∑ i, y i ^ 2) / 4), (tubeShift_gauss_integrable ι).const_mul _, ?_⟩
    intro w hw y
    refine (hbd w (hb hw) y).trans ?_
    beta_reduce
    rw [mul_assoc |C|]
    refine mul_le_mul_of_nonneg_left (tubeShift_gauss_bound y v _ _ ?_) (abs_nonneg _)
    have h1 : |w.im - w₀.im| ≤ ρ := by
      have h2 := Complex.abs_im_le_norm (w - w₀)
      rw [Complex.sub_im] at h2
      exact h2.trans (by simpa [dist_eq_norm] using hw)
    have h3 := abs_add_le (w.im - w₀.im) w₀.im
    rw [sub_add_cancel] at h3
    linarith
  have hper : ∀ w ∈ U, ∀ s : ℝ,
      (fun w => ∫ y, F w y) (w + (s : ℂ) * Complex.I) = (fun w => ∫ y, F w y) w := by
    intro w _ s
    have h1 : ∀ y : ι → ℝ, F (w + (s : ℂ) * Complex.I) y = F w (y + s • v) := by
      intro y
      simp only [F]
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    simp only [h1]
    exact integral_add_right_eq_self (F w) (s • v)
  have h0 : (0 : ℂ) ∈ U := ⟨by simp, by simp⟩
  have h1 : (1 : ℂ) ∈ U := ⟨by simp, by simp⟩
  have key := tubeShift_const_of_periodic U hUo hUc.isPreconnected _ hdiff hper h0 h1
  simp only [F, zero_mul, add_zero, one_mul] at key
  rw [key]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [v]
  congr 1
  funext i
  push_cast
  ring

theorem tubeShift : ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
    ∀ H : (ι → ℂ) → ℂ, DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω} →
    (∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2)) →
    ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω,
      (∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I)) =
        ∫ y : ι → ℝ, H (fun i => (x₂ i : ℂ) + (y i : ℂ) * Complex.I) := by
  intro ι _ Ω hΩ hc H hH hdec x₁ hx₁ x₂ hx₂
  refine hc.induction₂
    (fun a b => (∫ y : ι → ℝ, H (fun i => (a i : ℂ) + (y i : ℂ) * Complex.I)) =
      ∫ y : ι → ℝ, H (fun i => (b i : ℂ) + (y i : ℂ) * Complex.I)) ?_ ?_ ?_ hx₁ hx₂
  · intro x hx
    obtain ⟨R, hR, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hx)
    obtain ⟨C, hC⟩ := hdec _ hb (isCompact_closedBall x R)
    refine mem_nhdsWithin_of_mem_nhds ?_
    filter_upwards [Metric.closedBall_mem_nhds x (half_pos hR)] with y hy
    exact tubeShift_local Ω H hH x y R C hb hC (Metric.mem_closedBall.1 hy)
  · intro a b c _ _ _ h₁ h₂
    exact h₁.trans h₂
  · intro a b _ _ h
    exact h.symm

end GlobalTheory.CompanionTheory.EisTube
