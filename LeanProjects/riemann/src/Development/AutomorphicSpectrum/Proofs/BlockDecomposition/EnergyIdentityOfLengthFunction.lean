import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfDerivLeMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommute
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyEstimateOfLengthFunctionStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.Vanish

variable {n : ℕ} {W : Type} [NormedAddCommGroup W]

theorem dens_nonneg [NormedSpace ℝ W] (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) : 0 ≤ dens u s y := by
  unfold dens
  have : 0 ≤ ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  positivity

theorem sq_le_dens [NormedSpace ℝ W] (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) :
    ‖u s y‖ ^ 2 ≤ dens u s y := by
  unfold dens
  have : 0 ≤ ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith [sq_nonneg ‖dt u s y‖]

theorem dens_continuousOn [NormedSpace ℝ W] (u : ℝ → Mat n → W) (hu : Sm u) (s : ℝ) :
    ContinuousOn (dens u s) (GLs n) := by
  obtain ⟨h1, h2, h3, -, -⟩ := GlobalTheory.CompanionTheory.WaveSpd.sm_calculus u hu
  have a : ContinuousOn (dt u s) (GLs n) := ((GlobalTheory.CompanionTheory.WaveSpd.sm_calculus (dt u) h1).2.2.1 s).continuousOn
  have b : ContinuousOn (u s) (GLs n) := (h3 s).continuousOn
  have c : ∀ p : Ix n, ContinuousOn (Rt (hm p) u s) (GLs n) := fun p =>
    ((GlobalTheory.CompanionTheory.WaveSpd.sm_calculus (Rt (hm p) u) (h2 (hm p))).2.2.1 s).continuousOn
  unfold dens
  refine ((a.norm.pow 2).add (continuousOn_const.mul ?_)).add (b.norm.pow 2)
  exact continuousOn_finsetSum _ (fun p _ => (c p).norm.pow 2)

theorem weighted_zero [NormedSpace ℝ W] (ℓ : Mat n → ℝ) (hℓ : ContinuousOn ℓ (GLs n))
    (χ : ℝ → ℝ) (hχ : ∀ x, 1 ≤ x → χ x = 0) (u : ℝ → Mat n → W) (r : ℝ)
    (h0 : ∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) (h1 : ∀ y ∈ GLs n, dt u 0 y = 0)
    (y : Mat n) (hy : y ∈ GLs n) : χ (ℓ y - r) * dens u 0 y = 0 := by
  by_cases hc : 1 ≤ ℓ y - r
  · rw [hχ _ hc, zero_mul]
  · have hlt : ℓ y < r + 1 := by linarith
    have hnh : GLs n ∈ nhds y := isOpen_GLs.mem_nhds hy
    have hca : ContinuousAt ℓ y := hℓ.continuousAt hnh
    have hev : u 0 =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [hca.eventually_lt continuousAt_const hlt, hnh] with z hz hzG
      exact h0 z hzG hz
    have hR : ∀ p : Ix n, Rt (hm p) u 0 y = 0 := fun p => by
      change fderiv ℝ (u 0) y (y * hm p) = 0
      rw [hev.fderiv_eq]
      simp
    have hd : dens u 0 y = 0 := by
      unfold dens
      simp [hR, h1 y hy, h0 y hy hlt]
    rw [hd, mul_zero]

theorem energy_vanish : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) →
    ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) →
    (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) →
      ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) →
    ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) →
    (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W),
    (∀ s, ∀ y ∈ GLs n, dt (dt u) s y =
      (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) →
    ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), (∀ x, x ≤ 0 → χ x = 1) →
    (∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) → (∀ y ∈ GLs n, dt u 0 y = 0) →
    ∀ t : ℝ, 0 ≤ t → ∀ y ∈ GLs n, ℓ y + C * t ≤ r → u t y = 0 := by
  intro n W _ _ _ _ μ _ ℓ hℓ hcpt C₁ hC₁ hb hdiv χ hχs hχd hχ0 hχ1 u hu A hwave C hC r hχ2 h0 h1
    t ht y hy hyt
  obtain ⟨K, hK⟩ := GlobalTheory.T.energy_estimate_of_length_function μ ℓ hℓ hcpt C₁ hC₁ hb hdiv χ hχs hχd hχ0 hχ1 u hu A hwave C hC r
  choose e' he' hle using hK
  have hℓc : ContinuousOn ℓ (GLs n) := hℓ.continuousOn
  have hnn : ∀ (s : ℝ) (z : G n), 0 ≤ χ (ℓ z.val + C * s - r) * dens u s z.val := fun s z =>
    mul_nonneg (hχ0 _) (dens_nonneg u s _)
  have hzero : (∫ z : G n, χ (ℓ z.val + C * t - r) * dens u t z.val ∂μ) = 0 := by
    refine GlobalTheory.CompanionTheory.WaveSpd.GronwallZero.eq_zero_of_deriv_le_mul
      (fun s => ∫ z : G n, χ (ℓ z.val + C * s - r) * dens u s z.val ∂μ) e' K t ht he' hle
      (fun s => integral_nonneg (hnn s)) ?_
    have : ∀ z : G n, χ (ℓ z.val + C * 0 - r) * dens u 0 z.val = 0 := fun z => by
      have := weighted_zero ℓ hℓc χ hχ1 u r h0 h1 z.val (val_mem_GLs z)
      simpa using this
    simp only [this, integral_zero]
  have hval : Continuous (fun z : G n => z.val) := Units.continuous_val
  have hcont : Continuous (fun z : G n => χ (ℓ z.val + C * t - r) * dens u t z.val) := by
    have c1 : Continuous (fun z : G n => ℓ z.val) := hℓc.comp_continuous hval val_mem_GLs
    have c2 : Continuous (fun z : G n => dens u t z.val) :=
      (dens_continuousOn u hu t).comp_continuous hval val_mem_GLs
    exact (hχs.continuous.comp ((c1.add continuous_const).sub continuous_const)).mul c2
  have hsupp : HasCompactSupport (fun z : G n => χ (ℓ z.val + C * t - r) * dens u t z.val) := by
    refine HasCompactSupport.intro (hcpt (1 + r - C * t)) ?_
    intro z hz
    have hz' : 1 + r - C * t < ℓ z.val := not_le.1 hz
    have : χ (ℓ z.val + C * t - r) = 0 := hχ1 _ (by linarith)
    simp only [this, zero_mul]
  let yu : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero y hy
  have hyu : yu.val = y := rfl
  have hat : χ (ℓ y + C * t - r) * dens u t y = 0 := by
    by_contra hne
    have := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := yu) hsupp
      (fun z => hnn t z) (by simpa [hyu] using hne)
    exact this.ne' hzero
  rw [hχ2 _ (by linarith), one_mul] at hat
  have hsq := sq_le_dens u t y
  rw [hat] at hsq
  have : ‖u t y‖ ^ 2 = 0 := le_antisymm hsq (by positivity)
  simpa using this

end GlobalTheory.CompanionTheory.WaveSpd.Vanish
