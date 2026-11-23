import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval

lemma norm_le_norm_cat_left (A : Ad3.LR.M22) (y : Fin 2 → ℝ) : ‖A‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
  have h1 : ‖(cat A y) r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  refine le_trans ?_ h1
  fin_cases c
  · exact norm_le_pi_norm (cat A y r) 0
  · exact norm_le_pi_norm (cat A y r) 1

lemma norm_le_norm_cat_right (A : Ad3.LR.M22) (y : Fin 2 → ℝ) : ‖y‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  have h1 : ‖(cat A y) r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  exact le_trans (norm_le_pi_norm (cat A y r) 2) h1

theorem fz_decay_in_A : ∀ (Φ : Ad3.LR.Sw) (N : ℕ), ∃ C : ℝ, ∀ (A : Ad3.LR.M22) (ξ : Fin 2 → ℝ),
    (1 + ‖A‖) ^ N * ‖GlobalTheory.CompanionTheory.Parseval.fz Φ A ξ‖ ≤ C := by
  intro Φ N
  set C' : ℝ := 2 ^ (N + 3) *
    ((Finset.Iic ((N + 3, 0) : ℕ × ℕ)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ with hC'
  have hdec : ∀ X : Ad3.LR.M23, (1 + ‖X‖) ^ (N + 3) * ‖Φ X‖ ≤ C' := by
    intro X
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N + 3, 0))
      (k := N + 3) (n := 0) le_rfl le_rfl Φ X
    simpa [norm_iteratedFDeriv_zero] using this
  have hC'0 : 0 ≤ C' := by
    have h0 := hdec 0
    refine le_trans ?_ h0
    positivity
  have hint : Integrable (fun y : Fin 2 → ℝ => (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  set I : ℝ := ∫ y : Fin 2 → ℝ, (1 + ‖y‖) ^ (-(3 : ℝ)) with hI
  refine ⟨C' * I, fun A ξ => ?_⟩
  have hA : 0 < (1 + ‖A‖) ^ N := by positivity
  have hpt : ∀ y : Fin 2 → ℝ,
      ‖(Φ (cat A y) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))‖
        ≤ (C' / (1 + ‖A‖) ^ N) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y
    have hph : ‖Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))‖ = 1 := by
      have : (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ)) =
          ((2 * Real.pi * (ξ 0 * y 0 + ξ 1 * y 1) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hph, mul_one]
    have hy : 0 < 1 + ‖y‖ := by positivity
    have hy3 : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
      rw [Real.rpow_neg hy.le]
      norm_cast
    rw [hy3, div_mul_eq_mul_div, ← div_eq_mul_inv, div_div, le_div_iff₀ (by positivity)]
    have h1 : (1 + ‖A‖) ^ N ≤ (1 + ‖cat A y‖) ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_le_norm_cat_left A y]) N
    have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith [norm_le_norm_cat_right A y]) 3
    have h3 : (1 + ‖A‖) ^ N * (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ (N + 3) := by
      rw [pow_add]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    calc ‖Φ (cat A y)‖ * ((1 + ‖y‖) ^ 3 * (1 + ‖A‖) ^ N)
        ≤ ‖Φ (cat A y)‖ * (1 + ‖cat A y‖) ^ (N + 3) :=
          mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact h3) (norm_nonneg _)
      _ ≤ C' := by rw [mul_comm]; exact hdec _
  have hbound : ‖fz Φ A ξ‖ ≤ (C' / (1 + ‖A‖) ^ N) * I := by
    unfold fz
    have := norm_integral_le_of_norm_le (hint.const_mul (C' / (1 + ‖A‖) ^ N))
      (Filter.Eventually.of_forall hpt)
    rwa [integral_const_mul] at this
  calc (1 + ‖A‖) ^ N * ‖fz Φ A ξ‖
      ≤ (1 + ‖A‖) ^ N * ((C' / (1 + ‖A‖) ^ N) * I) :=
        mul_le_mul_of_nonneg_left hbound hA.le
    _ = C' * I := by field_simp

end GlobalTheory.CompanionTheory.Parseval
