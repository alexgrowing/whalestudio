import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOnBallOfEqOnPunctPolydiscCoveringExpImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

theorem combMat_mul_left {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (b * ε) = combMat l ε * bᵀ.map (Rat.cast : ℚ → ℂ) := by
  have h := combMat_add_mul l ε 0 bᵀ
  have h0 : combMat l (0 : Matrix (Fin g) (Fin r) ℚ) = 0 := by
    ext k j; simp [combMat]
  rwa [h0, zero_add, zero_add, Matrix.transpose_transpose] at h

theorem combMat_add {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) :
    combMat l (ε + φ) = combMat l ε + combMat l φ := by
  ext k j
  simp [combMat, add_mul, Finset.sum_add_distrib]

theorem isUnit_det_combMat_on_ball : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ) (rk D : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ → (∀ m (j : Fin g), j.val < rk → dl m j = 0) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 1)) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det := by
  intro n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ B hD hζ hstd hlam hc hdl hP hτ hB hper z hz
  choose I hI using hstd
  let sel : Matrix (Fin g) (Fin r₀) ℚ := Matrix.of fun j i => if i = I j then 1 else 0
  let Dl : Matrix (Fin g) (Fin g) ℂ := (sel * dl)ᵀ.map (Rat.cast : ℚ → ℂ)
  let G : Matrix (Fin g) (Fin g) ℂ := (sel * gm)ᵀ.map (Rat.cast : ℚ → ℂ)
  have hsel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, combMat (ζ z) sel = 1 := by
    intro z hz
    ext k j
    have h1 : combMat (ζ z) sel k j = ζ z (I j) k := by
      simp only [combMat, sel, Matrix.of_apply]
      rw [Finset.sum_eq_single (I j)]
      · simp
      · intro i _ hi; simp [hi]
      · simp
    rw [h1, hI j z hz, Matrix.one_apply, Pi.single_apply]
  have hBD : ∀ k, (B k).map (Int.cast : ℤ → ℂ) * Dl = 0 := by
    intro k
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply, Dl, Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < rk
    · simp [hdl _ l hl]
    · simp [hB k i l (Or.inr (not_lt.mp hl))]
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPc : ContinuousOn (fun z => combMat (ζ z) α) (Metric.ball (0 : Fin n → ℂ) 1) := by
    refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => ?_
    simp only [combMat, Matrix.of_apply]
    refine continuousOn_finset_sum _ fun m _ => continuousOn_const.mul ?_
    exact continuousOn_pi.1 (continuousOn_pi.1 hζ.continuousOn m) k
  have hτc : ContinuousOn τ₀ (Metric.ball (0 : Fin n → ℂ) 1) :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => (hτ k i).continuousOn
  have hQ : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
      p.1 * (G + (D : ℂ)⁻¹ • (p.2 * Dl))) := by fun_prop
  have hQc : ContinuousOn (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl)))
      (Metric.ball (0 : Fin n → ℂ) 1) := by
    have h := hQ.comp_continuousOn (hPc.prodMk hτc)
    simpa only [Function.comp_def] using h
  have key := GlobalTheory.eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix (Fin g) (Fin g) ℂ)
    (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl))) (fun _ => 1) le_rfl
    hQc continuousOn_const (by
      intro s hs hb
      have h1 := hsel _ hb
      rw [combMat_comb _ _ c sel (hlam s hs), hc, Matrix.mul_add, ← Matrix.mul_assoc sel gm, ← Matrix.mul_assoc sel dl,
        combMat_add, combMat_mul_left, combMat_mul_left, ← combMat_comb _ _ c α (hlam s hs)] at h1
      have h2 := congrArg (fun T => T * Dl) (hper s hs hb)
      simp only [perTau, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul, hBD, smul_zero, Finset.sum_const_zero,
        add_zero] at h2
      rw [← h2, smul_smul, inv_mul_cancel₀ hDc, one_smul, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hP s hs), Matrix.one_mul]
      exact h1) z hz
  exact Matrix.isUnit_det_of_right_inverse key

end GlobalTheory.PeriodFrame
