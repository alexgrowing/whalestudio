import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.TrDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula

noncomputable section

open Ad3.LR

namespace GlobalTheory.CompanionTheory.WeightRegular

theorem weight_eq_zero_neg_det (k : ℕ) (h : M22) (hd : (Matrix.of h).det < 0) : w0 k h = 0 := by
  have hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hn : ¬ 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hdi]
    exact not_lt.mpr (inv_nonpos.mpr hd.le)
  unfold w0 Wm
  rw [if_neg hn]
  simp

theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ ⊤ (fun h : M22 => h i j) :=
  (contDiff_apply_apply ℝ ℝ i j)

theorem contDiff_entryC (i j : Fin 2) : ContDiff ℝ ⊤ (fun h : M22 => ((h i j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_entry i j)

theorem contDiff_det : ContDiff ℝ ⊤ (fun h : M22 => (Matrix.of h).det) := by
  have : (fun h : M22 => (Matrix.of h).det) = fun h : M22 => h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    funext h
    simp [Matrix.det_fin_two]
  rw [this]
  exact ((contDiff_entry 0 0).mul (contDiff_entry 1 1)).sub
    ((contDiff_entry 0 1).mul (contDiff_entry 1 0))

theorem contDiffOn_weight_pos_det (k : ℕ) (hk : 3 ≤ k) :
    ContDiffOn ℝ ⊤ (w0 k) {h : M22 | 0 < (Matrix.of h).det} := by
  have hF : ContDiffOn ℝ ⊤ (fun h : M22 =>
      (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
        ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
        Complex.exp (2 * Real.pi * Complex.I *
          (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I))))
      {h : M22 | 0 < (Matrix.of h).det} := by
    intro h hh
    apply ContDiffAt.contDiffWithinAt
    have hα := GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hh
    have cα : ContDiffAt ℝ ⊤ (fun h : M22 => (h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) h :=
      ((contDiff_entryC 0 0).add ((contDiff_entryC 1 0).mul contDiff_const)).contDiffAt
    have cβ : ContDiffAt ℝ ⊤ (fun h : M22 => (h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) h :=
      ((contDiff_entryC 0 1).add ((contDiff_entryC 1 1).mul contDiff_const)).contDiffAt
    have cd : ContDiffAt ℝ ⊤ (fun h : M22 => (((Matrix.of h).det : ℝ) : ℂ)) h :=
      (Complex.ofRealCLM.contDiff.comp contDiff_det).contDiffAt
    have e : -(2 * (k : ℤ) - 1) = -(((2 * k - 1 : ℕ)) : ℤ) := by
      have : 1 ≤ 2 * k := by omega
      push_cast [Nat.cast_sub this]
      ring
    have cz : ContDiffAt ℝ ⊤ (fun h : M22 =>
        ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1))) h := by
      simp only [e, zpow_neg, zpow_natCast]
      exact (cα.pow _).inv (pow_ne_zero _ hα)
    have cq : ContDiffAt ℝ ⊤ (fun h : M22 =>
        ((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)) h := by
      simp only [div_eq_mul_inv]
      exact cβ.mul (cα.inv hα)
    have ce : ContDiffAt ℝ ⊤ (fun h : M22 => Complex.exp (2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)))) h :=
      (contDiffAt_const.mul cq).cexp
    exact ((cd.pow _).mul cz).mul ce
  exact hF.congr fun h hh => GlobalTheory.CompanionTheory.WeightClosed.main k hk h hh

theorem main_analytic (k : ℕ) (hk : 3 ≤ k) :
    (∀ h : M22, (Matrix.of h).det < 0 → w0 k h = 0) ∧
      ContDiffOn ℝ ⊤ (w0 k) {h : M22 | 0 < (Matrix.of h).det} :=
  ⟨fun h hd => weight_eq_zero_neg_det k h hd, contDiffOn_weight_pos_det k hk⟩

theorem main : Ad3.LR.DTr.WeightVanishesNegDetSmoothPosDet := fun k hk =>
  ⟨(main_analytic k hk).1, (main_analytic k hk).2.of_le le_top⟩

end GlobalTheory.CompanionTheory.WeightRegular
