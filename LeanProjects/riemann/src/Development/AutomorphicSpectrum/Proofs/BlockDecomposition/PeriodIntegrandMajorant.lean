import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveIntegralBoundOfParts

noncomputable section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.PerUInt

theorem inv_pow_le_phi_prod (h : Ad3.LR.M22) (N : ℕ) (hN : 8 ≤ N) :
    1 / (1 + ‖h‖) ^ N ≤ phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) := by
  have entry : ∀ i j, 1 + |h i j| ≤ 1 + ‖h‖ := by
    intro i j
    have h1 : ‖h i j‖ ≤ ‖h i‖ := norm_le_pi_norm (h i) j
    have h2 : ‖h i‖ ≤ ‖h‖ := norm_le_pi_norm h i
    have h3 : |h i j| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using h1.trans h2
    linarith
  have ht : 1 ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
  have sq : ∀ i j, (1 + |h i j|) ^ 2 ≤ (1 + ‖h‖) ^ 2 := fun i j =>
    pow_le_pow_left₀ (by positivity) (entry i j) 2
  have hP : (1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2) ≤
      (1 + ‖h‖) ^ N := by
    calc (1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2)
        ≤ (1 + ‖h‖) ^ 2 * (1 + ‖h‖) ^ 2 * ((1 + ‖h‖) ^ 2 * (1 + ‖h‖) ^ 2) := by
          have a := sq 0 0
          have b := sq 1 0
          have c := sq 0 1
          have d := sq 1 1
          gcongr
      _ = (1 + ‖h‖) ^ 8 := by ring
      _ ≤ (1 + ‖h‖) ^ N := pow_le_pow_right₀ ht hN
  have hphi : phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) =
      ((1 + |h 0 0|) ^ 2 * (1 + |h 1 0|) ^ 2 * ((1 + |h 0 1|) ^ 2 * (1 + |h 1 1|) ^ 2))⁻¹ := by
    simp only [phi, mul_inv]
  rw [hphi, one_div]
  exact inv_anti₀ (by positivity) hP

theorem kernel_exponents (k : ℕ) (σ Y c E : ℝ) (hY : 0 < Y) (hc : 0 < c) :
    (Y ^ ((2 * (k : ℝ) - 1) / 2) * E) * (Y * c) ^ (-(3 : ℝ) / 2) *
        ((c / 2) ^ ((1 : ℝ) / 2) / (Y * c)) ^ (σ - 1) =
      2 ^ ((1 - σ) / 2) * (Y ^ ((k : ℝ) - 1 - σ) * E * c ^ (-1 - σ / 2)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hw : 0 < (c / 2) ^ ((1 : ℝ) / 2) / (Y * c) := by positivity
  have hlog : Real.log ((c / 2) ^ ((1 : ℝ) / 2) / (Y * c)) =
      (Real.log c - Real.log 2) / 2 - (Real.log Y + Real.log c) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_div hc.ne' h2.ne', Real.log_mul hY.ne' hc.ne']
    ring
  rw [Real.rpow_def_of_pos hY, Real.rpow_def_of_pos (mul_pos hY hc), Real.rpow_def_of_pos hw,
    Real.rpow_def_of_pos h2, Real.rpow_def_of_pos hY, Real.rpow_def_of_pos hc, hlog,
    Real.log_mul hY.ne' hc.ne']
  have e : ∀ a b c' : ℝ, Real.exp a * E * Real.exp b * Real.exp c' =
      Real.exp (a + b + c') * E := by
    intro a b c'
    rw [Real.exp_add, Real.exp_add]
    ring
  have e' : ∀ a b c' : ℝ, Real.exp a * (Real.exp b * E * Real.exp c') =
      Real.exp (a + b + c') * E := by
    intro a b c'
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [e, e']
  congr 2
  ring

theorem norm_Wm_inv (k : ℕ) (h : Ad3.LR.M22) (hD : 0 < (Matrix.of h).det)
    (hc : 0 < h 0 0 ^ 2 + h 1 0 ^ 2) :
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ =
      ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) ^ ((2 * (k : ℝ) - 1) / 2) *
        Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)))) := by
  obtain ⟨e0, e1⟩ := GlobalTheory.CompanionTheory.PrimalInt.inv_row h hD.ne'
  have hdet : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hone : Ad3.LR.C.d2 1 = 1 := by
    simp [Ad3.LR.C.d2, Matrix.one_fin_two]
  have hW := GlobalTheory.CompanionTheory.AbsWm.norm_Wm k (Matrix.of h)⁻¹ 1 (by
    rw [one_mul, hdet]
    exact inv_pos.2 hD)
  rw [hone, one_mul, one_mul] at hW
  have hNR : Complex.normSq (GlobalTheory.CompanionTheory.WmFE.jj (Matrix.of h)⁻¹) =
      (h 0 0 ^ 2 + h 1 0 ^ 2) / (Matrix.of h).det ^ 2 := by
    have : Complex.normSq (GlobalTheory.CompanionTheory.WmFE.jj (Matrix.of h)⁻¹) =
        ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 +
          ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ^ 2 := by
      simp [GlobalTheory.CompanionTheory.WmFE.jj, Complex.normSq_apply]
      ring
    rw [this, e0, e1]
    field_simp
    ring
  rw [hW, hNR, hdet]
  generalize (Matrix.of h).det = D at hD
  generalize h 0 0 ^ 2 + h 1 0 ^ 2 = c at hc
  have hY : D⁻¹ = D / c * (c / D ^ 2) := by
    field_simp
  have hE : 2 * Real.pi * D⁻¹ / (c / D ^ 2) = 2 * Real.pi * (D / c) := by
    field_simp
  have hYp : 0 < D / c := by positivity
  have hNp : 0 < c / D ^ 2 := by positivity
  rw [hE]
  congr 1
  rw [hY, Real.mul_rpow hYp.le hNp.le, mul_assoc, ← Real.rpow_add hNp]
  simp

theorem pointwise_gamma_bound : ∀ (k : ℕ), 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 8 ≤ N →
    ∃ C : ℝ, ∀ h : Ad3.LR.M22, (Matrix.of h).det ≠ 0 →
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) * ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N ≤
      C * (GlobalTheory.CompanionTheory.PerUInt.gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
        (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 0) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 0) * (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 1) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 1)))) := by
  intro k _ σ _ h1 N hN
  refine ⟨2 ^ ((1 - σ) / 2), fun h hd => ?_⟩
  have hC : (0 : ℝ) ≤ 2 ^ ((1 - σ) / 2) := by positivity
  have hΦ : 0 ≤ phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1)) :=
    mul_nonneg (mul_nonneg (phi_nonneg _) (phi_nonneg _)) (mul_nonneg (phi_nonneg _) (phi_nonneg _))
  have hc0 : 0 ≤ h 0 0 ^ 2 + h 1 0 ^ 2 := by positivity
  rcases lt_or_gt_of_ne hd with hneg | hD
  · have hdet : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    have hW : Ad3.LR.Wm k (Matrix.of h)⁻¹ = 0 := by
      have : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
        rw [hdet]
        exact not_lt.2 (inv_lt_zero.2 hneg).le
      unfold Ad3.LR.Wm
      exact if_neg this
    rw [hW]
    simp only [norm_zero, zero_mul, zero_div]
    exact mul_nonneg hC (mul_nonneg (mul_nonneg (gk_nonneg _ _ _) (Real.rpow_nonneg hc0 _)) hΦ)
  · have hc : 0 < h 0 0 ^ 2 + h 1 0 ^ 2 := by
      rcases hc0.lt_or_eq with hp | hz
      · exact hp
      · exfalso
        have ha : h 0 0 = 0 := by nlinarith [sq_nonneg (h 0 0), sq_nonneg (h 1 0)]
        have hb : h 1 0 = 0 := by nlinarith [sq_nonneg (h 0 0), sq_nonneg (h 1 0)]
        apply hd
        simp [Matrix.det_fin_two, ha, hb]
    obtain ⟨e0, e1⟩ := GlobalTheory.CompanionTheory.PrimalInt.inv_row h hd
    have b0 : |((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0| ≤ ‖Ad3.LR.B.eta h‖ := by
      simpa [Ad3.LR.B.eta] using norm_le_pi_norm (Ad3.LR.B.eta h) 0
    have b1 : |((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1| ≤ ‖Ad3.LR.B.eta h‖ := by
      simpa [Ad3.LR.B.eta] using norm_le_pi_norm (Ad3.LR.B.eta h) 1
    rw [e0, abs_div, abs_neg, abs_of_pos hD, div_le_iff₀ hD] at b0
    rw [e1, abs_div, abs_of_pos hD, div_le_iff₀ hD] at b1
    have hw : ((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det ≤
        ‖Ad3.LR.B.eta h‖ := by
      rw [div_le_iff₀ hD, ← Real.sqrt_eq_rpow]
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      have s0 : h 1 0 ^ 2 ≤ (‖Ad3.LR.B.eta h‖ * (Matrix.of h).det) ^ 2 := by
        rw [← sq_abs (h 1 0)]
        exact pow_le_pow_left₀ (abs_nonneg _) b0 2
      have s1 : h 0 0 ^ 2 ≤ (‖Ad3.LR.B.eta h‖ * (Matrix.of h).det) ^ 2 := by
        rw [← sq_abs (h 0 0)]
        exact pow_le_pow_left₀ (abs_nonneg _) b1 2
      linarith
    have hwpos : 0 < ((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det := by
      positivity
    have hE : ‖Ad3.LR.B.eta h‖ ^ (σ - 1) ≤
        (((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det) ^ (σ - 1) :=
      Real.rpow_le_rpow_of_nonpos hwpos hw (by linarith)
    have hdec := inv_pow_le_phi_prod h N hN
    have hYp : 0 < (Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2) := div_pos hD hc
    have hDY : (Matrix.of h).det =
        (Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2) * (h 0 0 ^ 2 + h 1 0 ^ 2) := by
      field_simp
    have hker := kernel_exponents k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2))
      (h 0 0 ^ 2 + h 1 0 ^ 2)
      (Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2))))) hYp hc
    rw [← hDY] at hker
    have hgk : gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) =
        ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) ^ ((k : ℝ) - 1 - σ) *
          Real.exp (-(2 * Real.pi * ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)))) := by
      simp [gk, hYp]
    rw [abs_of_pos hD]
    calc ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
          ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N
        = (‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
            ‖Ad3.LR.B.eta h‖ ^ (σ - 1)) * (1 / (1 + ‖h‖) ^ N) := by ring
      _ ≤ (‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * (Matrix.of h).det ^ (-(3 : ℝ) / 2) *
            (((h 0 0 ^ 2 + h 1 0 ^ 2) / 2) ^ ((1 : ℝ) / 2) / (Matrix.of h).det) ^ (σ - 1)) *
            (phi (h 0 0) * phi (h 1 0) * (phi (h 0 1) * phi (h 1 1))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hE (by positivity)) hdec (by positivity)
            (by positivity)
      _ = _ := by
          rw [norm_Wm_inv k h hD hc, hker, hgk]
          ring

end GlobalTheory.CompanionTheory.PerUInt
