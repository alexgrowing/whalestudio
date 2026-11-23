import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.FSStatements

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.FSW

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

theorem fdegH_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {μG : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)} {d : ℝ}
    (hS : 0 < d ∧ ∀ v w v' w' : H,
      Integrable (fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w : H} (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, h⟩ := hS
  obtain ⟨_, heq⟩ := h w w w w
  have h1 : ∀ x : Mt k r, ⟪w, σ (Matrix.of x) w⟫_ℂ * star ⟪w, σ (Matrix.of x) w⟫_ℂ =
      ((‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hR : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    have h3 : ((∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      simp_rw [← h1]
      rw [heq, inner_self_eq_norm_sq_to_K, Complex.ofReal_div, Complex.ofReal_pow]
      ring_nf
      try exact mul_comm _ _
    exact_mod_cast h3
  have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  show ‖w‖ ^ 4 / ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = d
  rw [hR]
  field_simp

end PI.WBL.FSW
