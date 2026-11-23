import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrablePhiF

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem one_mem_uh : (1 : Mx k r) ∈ UH (Hpk k r) := by
  simp [UH]

theorem mem_DD {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)) (w0 : H)
    {t : Mx k r} (ht : t ∈ UH (Hpk k r)) : σ t w0 ∈ DDsp σ w0 := Submodule.subset_span ⟨t, ht, rfl⟩

theorem fdeg_of_schur {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {μG : Measure (Mt k r)} {w0 : H} (hw : w0 ≠ 0) {d : ℝ} (hd : 0 < d)
    (hS : ∫ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ ∂μG =
      ⟪w0, w0⟫_ℂ * ⟪w0, w0⟫_ℂ / (d : ℂ)) :
    PI.BesselPeriodGGP.fdegH μG σ w0 = d := by

  have hpt : ∀ x, ⟪w0, σ (Matrix.of x) w0⟫_ℂ * star ⟪w0, σ (Matrix.of x) w0⟫_ℂ =
      ((‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [show star ⟪w0, σ (Matrix.of x) w0⟫_ℂ = (starRingEnd ℂ) ⟪w0, σ (Matrix.of x) w0⟫_ℂ from rfl,
      RCLike.mul_conj]
    norm_cast
  simp_rw [hpt] at hS
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hS
  have hI : (∫ x, ‖⟪w0, σ (Matrix.of x) w0⟫_ℂ‖ ^ 2 ∂μG) = ‖w0‖ ^ 4 / d := by
    have h2 : ((‖w0‖ ^ 4 / d : ℝ) : ℂ) = (‖w0‖ : ℂ) ^ 2 * (‖w0‖ : ℂ) ^ 2 / (d : ℂ) := by
      push_cast; ring
    exact_mod_cast hS.trans h2.symm
  have hw' : ‖w0‖ ≠ 0 := norm_ne_zero_iff.2 hw
  simp only [PI.BesselPeriodGGP.fdegH]
  rw [hI]
  field_simp

end Formalism.FourierDecayAlt.P.S3dx6
