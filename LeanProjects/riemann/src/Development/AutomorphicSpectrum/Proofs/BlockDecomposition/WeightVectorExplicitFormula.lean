import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD

noncomputable section

open Ad3.LR

namespace GlobalTheory.CompanionTheory.WeightClosed

theorem real_factor (k : ℕ) (hk : 1 ≤ k) (Δ : ℝ) (hΔ : 0 < Δ) :
    (Δ⁻¹) ^ ((2 * (k : ℝ) - 1) / 2) * Δ ^ (-(1 : ℝ) / 2) * Δ ^ (2 * (k : ℤ) - 1) = Δ ^ (k - 1) := by
  have h1 : Δ ^ (2 * (k : ℤ) - 1) = Δ ^ (2 * (k : ℝ) - 1) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [h1, Real.inv_rpow hΔ.le, ← Real.rpow_neg hΔ.le, ← Real.rpow_add hΔ, ← Real.rpow_add hΔ,
    ← Real.rpow_natCast]
  congr 1
  push_cast [Nat.cast_sub hk]
  ring

theorem inv_entries (h : M22) :
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = ((Matrix.of h).det)⁻¹ * h 1 1 ∧
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(((Matrix.of h).det)⁻¹ * h 0 1) ∧
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -(((Matrix.of h).det)⁻¹ * h 1 0) ∧
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = ((Matrix.of h).det)⁻¹ * h 0 0 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  simp

theorem alpha_ne_zero (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    (h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I ≠ 0 := by
  intro h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp at hre him
  rw [Matrix.det_fin_two] at hΔ
  simp [hre, him] at hΔ

theorem finiteRing_sq_sub_mul_sq_eq_of_card (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    w0 k h = (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
      ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
      Complex.exp (2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I))) := by
  have hα := alpha_ne_zero h hΔ
  obtain ⟨i00, i01, i10, i11⟩ := inv_entries h
  have hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hreal := real_factor k (by omega) _ hΔ
  have hD : (((Matrix.of h).det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have hsg : sg (Matrix.of h).det = 1 := by
    unfold sg
    exact if_neg (not_lt.mpr hΔ.le)
  have hdp : 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hdi]
    exact inv_pos.mpr hΔ
  have hab : |(Matrix.of h).det| = (Matrix.of h).det := abs_of_pos hΔ
  have e1 : ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ) -
      ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * Complex.I =
      ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [i11, i10]
    push_cast
    field_simp
    ring
  have e2 : ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ) -
      ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * Complex.I =
      -((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [i01, i00]
    push_cast
    field_simp
    ring
  have hz : (((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ)) ^
      (-(2 * (k : ℤ) - 1)) = ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
        (((Matrix.of h).det : ℝ) : ℂ) ^ (2 * (k : ℤ) - 1) := by
    rw [div_zpow, zpow_neg (((Matrix.of h).det : ℝ) : ℂ), div_inv_eq_mul]
  have hq : -2 * (Real.pi : ℂ) * Complex.I *
      ((-((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ)) /
        (((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ))) =
      2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)) := by
    field_simp
  have hc : (((((Matrix.of h).det)⁻¹ ^ ((2 * (k : ℝ) - 1) / 2) : ℝ)) : ℂ) *
      (((Matrix.of h).det ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      (((Matrix.of h).det : ℝ) : ℂ) ^ (2 * (k : ℤ) - 1) =
      (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hreal
    simpa using this
  unfold w0 Wm
  rw [if_pos hdp, hsg, hab, hdi, e1, e2, hz, hq]
  linear_combination (((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
    Complex.exp (2 * Real.pi * Complex.I *
      (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)))) * hc

end GlobalTheory.CompanionTheory.WeightClosed

theorem GlobalTheory.CompanionTheory.WeightClosed.main : ∀ (k : ℕ), 3 ≤ k → ∀ h : Ad3.LR.M22, 0 < (Matrix.of h).det → Ad3.LR.w0 k h = (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) * ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I))) :=
  GlobalTheory.CompanionTheory.WeightClosed.finiteRing_sq_sub_mul_sq_eq_of_card
