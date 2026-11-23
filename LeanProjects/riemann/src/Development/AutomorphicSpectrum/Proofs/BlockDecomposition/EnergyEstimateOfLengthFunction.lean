import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommuteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivIntegralCompactSupportStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityTimeDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensitySmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyDensityPointwiseEstimateStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.LocEnergy

variable {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def cw (ℓ : Mat n → ℝ) (χ : ℝ → ℝ) (C r s : ℝ) (y : Mat n) : ℝ := χ (ℓ y + C * s - r)

theorem sm_cw {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (C r : ℝ) (hℓ : ContDiffOn ℝ ∞ ℓ (GLs n))
    (hχ : ContDiff ℝ ∞ χ) : Sm (cw ℓ χ C r) := by
  have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => ℓ q.2 + C * q.1 - r) (Set.univ ×ˢ GLs n) := by
    have h2 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => ℓ q.2) (Set.univ ×ˢ GLs n) :=
      hℓ.comp contDiff_snd.contDiffOn (fun q hq => hq.2)
    have h3 : ContDiffOn ℝ ∞ (fun q : ℝ × Mat n => C * q.1) (Set.univ ×ˢ GLs n) :=
      (contDiff_const.mul contDiff_fst).contDiffOn
    exact (h2.add h3).sub contDiffOn_const
  exact hχ.comp_contDiffOn h1

theorem sm_mul {f g : ℝ → Mat n → ℝ} (hf : Sm f) (hg : Sm g) : Sm fun s y => f s y * g s y :=
  ContDiffOn.mul hf hg

theorem hasDerivAt_chi {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (a : ℝ) : HasDerivAt χ (deriv χ a) a :=
  ((hχ.differentiable (by simp)) a).hasDerivAt

theorem hasDerivAt_cw {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (ℓ : Mat n → ℝ) (C r s : ℝ) (y : Mat n) :
    HasDerivAt (fun s' => cw ℓ χ C r s' y) (deriv χ (ℓ y + C * s - r) * C) s := by
  have h1 : HasDerivAt (fun s' : ℝ => ℓ y + C * s' - r) C s := by
    simpa using (((hasDerivAt_id s).const_mul C).const_add (ℓ y)).sub_const r
  exact (hasDerivAt_chi hχ _).comp s h1

theorem dt_rho {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {u : ℝ → Mat n → W} (hu : Sm u)
    (C r s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    dt (fun s y => cw ℓ χ C r s y * dens u s y) s y =
      deriv χ (ℓ y + C * s - r) * C * dens u s y + cw ℓ χ C r s y *
        (2 * ⟪dt (dt u) s y, dt u s y⟫_ℝ
          + (1 / 2) * ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ
          + 2 * ⟪dt u s y, u s y⟫_ℝ) :=
  ((hasDerivAt_cw hχ ℓ C r s y).mul (GlobalTheory.T.energy_density_time_derivative u hu s y hy)).deriv

theorem rr_cw_inner {ℓ : Mat n → ℝ} {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (C r s : ℝ)
    {f g : Mat n → W} {y : Mat n} (hℓ : DifferentiableAt ℝ ℓ y) (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (X : Mat n) :
    Rr X (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y =
      deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * X) * ⟪f y, g y⟫_ℝ +
        cw ℓ χ C r s y * (⟪Rr X f y, g y⟫_ℝ + ⟪f y, Rr X g y⟫_ℝ) := by
  have h1 : HasFDerivAt (fun y' => cw ℓ χ C r s y')
      (deriv χ (ℓ y + C * s - r) • fderiv ℝ ℓ y) y :=
    (hasDerivAt_chi hχ _).comp_hasFDerivAt y ((hℓ.hasFDerivAt.add_const (C * s)).sub_const r)
  have h2 : HasFDerivAt (fun t => ⟪f t, g t⟫_ℝ) (fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y) y :=
    (hf.inner ℝ hg).hasFDerivAt
  have h3 : HasFDerivAt (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) _ y := h1.mul h2
  have h4 : fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y (y * X) =
      ⟪f y, Rr X g y⟫_ℝ + ⟪Rr X f y, g y⟫_ℝ := fderiv_inner_apply ℝ hf hg (y * X)
  have h5 : fderiv ℝ (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y (y * X) =
      cw ℓ χ C r s y * fderiv ℝ (fun t => ⟪f t, g t⟫_ℝ) y (y * X) +
        ⟪f y, g y⟫_ℝ * (deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * X)) := by
    rw [h3.fderiv]
    rfl
  show fderiv ℝ (fun y' => cw ℓ χ C r s y' * ⟪f y', g y'⟫_ℝ) y (y * X) = _
  rw [h5, h4]
  ring

theorem diffAt_of_sm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {y : Mat n} (hy : y ∈ GLs n) : DifferentiableAt ℝ f y :=
  (hf.contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)

theorem pt_bound {ℓ : Mat n → ℝ} (hℓ : ContDiffOn ℝ ∞ ℓ (GLs n)) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ' : ∀ x, deriv χ x ≤ 0) (hχ0 : ∀ x, 0 ≤ χ x)
    {u : ℝ → Mat n → W} (hu : Sm u) (A : W →L[ℝ] W)
    (hwave : ∀ s, ∀ y ∈ GLs n, dt (dt u) s y =
      (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y))
    {C₁ C : ℝ} (r : ℝ) (hC₁ : 0 ≤ C₁) (hC : C₁ * (1 + Fintype.card (Ix n)) ≤ C)
    (hL : ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁)
    (s : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    dt (fun s y => cw ℓ χ C r s y * dens u s y) s y -
        (1 / 2) * ∑ p : Ix n,
          Rr (hm p) (fun y' => cw ℓ χ C r s y' * ⟪Rt (hm p) u s y', dt u s y'⟫_ℝ) y ≤
      (‖A‖ + 1) * (cw ℓ χ C r s y * dens u s y) := by
  have hdu := (GlobalTheory.T.smooth_time_right_derivatives_commute u hu).1
  have hRt := (GlobalTheory.T.smooth_time_right_derivatives_commute u hu).2.1
  have hℓd := diffAt_of_sm hℓ hy
  have hw : DifferentiableAt ℝ (dt u s) y := diffAt_of_sm ((GlobalTheory.T.smooth_time_right_derivatives_commute _ hdu).2.2.1 s) hy
  have hY : ∀ p : Ix n, DifferentiableAt ℝ (Rt (hm p) u s) y :=
    fun p => diffAt_of_sm ((GlobalTheory.T.smooth_time_right_derivatives_commute _ (hRt _)).2.2.1 s) hy
  have hpt := GlobalTheory.T.energy_density_pointwise_estimate (dt u s y) (u s y) (fun p : Ix n => Rt (hm p) u s y)
    (fun p => fderiv ℝ ℓ y (y * hm p)) A C₁ C (deriv χ (ℓ y + C * s - r)) (cw ℓ χ C r s y)
    hC₁ hC (hχ' _) (hχ0 _) (fun p => hL y hy p)
  have hD : ‖dt u s y‖ ^ 2 + (1 / 4) * ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 + ‖u s y‖ ^ 2
      = dens u s y := rfl
  rw [hD] at hpt
  have e1 : ⟪(1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y), dt u s y⟫_ℝ
      = (1 / 4) * ∑ p : Ix n, ⟪Rr (hm p) (Rt (hm p) u s) y, dt u s y⟫_ℝ
        + ⟪A (u s y), dt u s y⟫_ℝ := by
    rw [inner_add_left, real_inner_smul_left, sum_inner]
  have e2 : ∑ p : Ix n,
      Rr (hm p) (fun y' => cw ℓ χ C r s y' * ⟪Rt (hm p) u s y', dt u s y'⟫_ℝ) y =
      ∑ p : Ix n, deriv χ (ℓ y + C * s - r) * fderiv ℝ ℓ y (y * hm p) *
          ⟪Rt (hm p) u s y, dt u s y⟫_ℝ +
        cw ℓ χ C r s y * (∑ p : Ix n, ⟪Rr (hm p) (Rt (hm p) u s) y, dt u s y⟫_ℝ +
          ∑ p : Ix n, ⟪Rr (hm p) (dt u s) y, Rt (hm p) u s y⟫_ℝ) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rr_cw_inner hχ C r s hℓd (hY p) hw (hm p), real_inner_comm (Rt (hm p) u s y)]
  rw [dt_rho hχ hu C r s hy, hwave s y hy, e1, e2]
  refine le_trans (le_of_eq ?_) hpt
  ring

theorem integrable_of_val [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] {f : Mat n → ℝ} (hf : ContinuousOn f (GLs n)) {K : Set (G n)}
    (hK : IsCompact K) (h : ∀ y : G n, y ∉ K → f y.val = 0) :
    Integrable (fun y : G n => f y.val) μ :=
  (hf.comp_continuous Units.continuous_val val_mem_GLs).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hK h)

theorem energy_diff_ineq : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) → ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) → (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) → ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) → (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W), (∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) → ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), ∃ K : ℝ, ∀ s, ∃ e' : ℝ, HasDerivAt (fun s' => ∫ y : G n, χ (ℓ y.val + C * s' - r) * dens u s' y.val ∂μ) e' s ∧ e' ≤ K * ∫ y : G n, χ (ℓ y.val + C * s - r) * dens u s y.val ∂μ := by
  intro n W _ _ _ _ μ _ ℓ hℓ hcpt C₁ hC₁ hL hIBP χ hχ hχ' hχ0 hχ1 u hu A hwave C hC r
  refine ⟨‖A‖ + 1, fun s => ?_⟩
  have hC0 : 0 ≤ C := le_trans (mul_nonneg hC₁ (by positivity)) hC
  have hdu := (GlobalTheory.T.smooth_time_right_derivatives_commute u hu).1
  have hcw := sm_cw C r hℓ hχ
  let ρ : ℝ → Mat n → ℝ := fun s y => cw ℓ χ C r s y * dens u s y
  have hρ : Sm ρ := sm_mul hcw (GlobalTheory.T.energy_density_smooth u hu).1
  let Ψ : Ix n → ℝ → Mat n → ℝ :=
    fun p s y => cw ℓ χ C r s y * ⟪Rt (hm p) u s y, dt u s y⟫_ℝ
  have hΨ : ∀ p, Sm (Ψ p) := fun p => sm_mul hcw ((GlobalTheory.T.energy_density_smooth u hu).2 _ _ hdu)
  obtain ⟨R, hR⟩ : ∃ R, R = r + 1 + C * (|s| + 1) := ⟨_, rfl⟩
  have hK : IsCompact {y : G n | ℓ y.val ≤ R} := hcpt R
  have hvan : ∀ s' ∈ Metric.ball s 1, ∀ y : G n, y ∉ {y : G n | ℓ y.val ≤ R} →
      ρ s' y.val = 0 := by
    intro s' hs' y hy
    have hy' : R < ℓ y.val := not_le.1 hy
    have h0 : 0 ≤ |s| + 1 + s' := by
      have h1 := neg_abs_le s
      have h2 := (abs_lt.1 (Real.dist_eq s' s ▸ Metric.mem_ball.1 hs')).1
      linarith
    have h3 := mul_nonneg hC0 h0
    have h4 : 1 ≤ ℓ y.val + C * s' - r := by rw [hR] at hy'; nlinarith
    simp only [ρ, cw, hχ1 _ h4, zero_mul]
  have hder := GlobalTheory.T.deriv_integral_compact_support μ ρ hρ _ hK s 1 one_pos hvan
  refine ⟨_, hder, ?_⟩
  have hdtvan : ∀ y : G n, y ∉ {y : G n | ℓ y.val ≤ R} → dt ρ s y.val = 0 := by
    intro y hy
    have h1 : (fun r' => ρ r' y.val) =ᶠ[nhds s] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds s one_pos] with s' hs' using hvan s' hs' y hy
    show deriv (fun r' => ρ r' y.val) s = 0
    rw [h1.deriv_eq]; simp
  have I_dt := integrable_of_val μ
    ((GlobalTheory.T.smooth_time_right_derivatives_commute _ (GlobalTheory.T.smooth_time_right_derivatives_commute _ hρ).1).2.2.1 s).continuousOn hK hdtvan
  have I_ρ := integrable_of_val μ ((GlobalTheory.T.smooth_time_right_derivatives_commute _ hρ).2.2.1 s).continuousOn hK
    (hvan s (Metric.mem_ball_self one_pos))
  have hRs : r + 1 - C * s ≤ R := by
    have h1 := neg_abs_le s
    have h2 : 0 ≤ C * (|s| + 1 + s) := mul_nonneg hC0 (by linarith)
    rw [hR]; nlinarith
  have hrrvan : ∀ (p : Ix n) (y : G n), y ∉ {y : G n | ℓ y.val ≤ R} →
      Rr (hm p) (Ψ p s) y.val = 0 := by
    intro p y hy
    have hy' : R < ℓ y.val := not_le.1 hy
    have hcont : ContinuousAt ℓ y.val := (diffAt_of_sm hℓ (val_mem_GLs y)).continuousAt
    have h1 : Ψ p s =ᶠ[nhds y.val] fun _ => 0 := by
      filter_upwards [hcont.eventually (lt_mem_nhds hy')] with z hz
      have h4 : 1 ≤ ℓ z + C * s - r := by linarith
      simp only [Ψ, cw, hχ1 _ h4, zero_mul]
    show fderiv ℝ (Ψ p s) y.val _ = 0
    rw [h1.fderiv_eq]; simp
  have I_rr : ∀ p : Ix n, Integrable (fun y : G n => Rr (hm p) (Ψ p s) y.val) μ := fun p =>
    integrable_of_val μ
      ((GlobalTheory.T.smooth_time_right_derivatives_commute _ ((GlobalTheory.T.smooth_time_right_derivatives_commute _ (hΨ p)).2.1 (hm p))).2.2.1 s).continuousOn hK
      (hrrvan p)
  have hZ : ∀ p : Ix n, ∫ y : G n, Rr (hm p) (Ψ p s) y.val ∂μ = 0 := fun p =>
    hIBP (Ψ p s) ((GlobalTheory.T.smooth_time_right_derivatives_commute _ (hΨ p)).2.2.1 s)
      ⟨r + 1 - C * s, fun y _ hy => by
        have h4 : 1 ≤ ℓ y + C * s - r := by linarith
        simp only [Ψ, cw, hχ1 _ h4, zero_mul]⟩ (hm p)
  have I_sum : Integrable (fun y : G n => (1 / 2 : ℝ) * ∑ p : Ix n, Rr (hm p) (Ψ p s) y.val) μ :=
    (integrable_finset_sum _ fun p _ => I_rr p).const_mul _
  calc ∫ y : G n, dt ρ s y.val ∂μ
      = ∫ y : G n, (dt ρ s y.val - (1 / 2 : ℝ) * ∑ p : Ix n, Rr (hm p) (Ψ p s) y.val) ∂μ := by
        rw [integral_sub I_dt I_sum, integral_const_mul,
          integral_finset_sum _ fun p _ => I_rr p]
        simp [hZ]
    _ ≤ ∫ y : G n, (‖A‖ + 1) * ρ s y.val ∂μ :=
        integral_mono (I_dt.sub I_sum) (I_ρ.const_mul _) fun y =>
          pt_bound hℓ hχ hχ' hχ0 hu A hwave r hC₁ hC hL s (val_mem_GLs y)
    _ = (‖A‖ + 1) * ∫ y : G n, ρ s y.val ∂μ := integral_const_mul _ _

end GlobalTheory.CompanionTheory.WaveSpd.LocEnergy
