import Formalism.HermitianCurvature.HermitianCurvatureProofs.OoConvOf
import Formalism.FormalDegreeBessel.FinalG

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem coef_eq {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) {z Y z' : Mx k r}
    (hz : z ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hY : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hz' : z' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (w : H) :
    ⟪σ z w, σ Y (σ z' w)⟫_ℂ = ⟪w, σ (z⁻¹ * Y * z') w⟫_ℂ := by
  have hzi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hz
  have hiso := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hds).2 z hz
  have hM : z⁻¹ * Y * z' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hzi.1 hY) hz'
  have h1 : σ Y (σ z' w) = σ z (σ (z⁻¹ * Y * z') w) := by
    have e1 : σ (Y * z') = (σ Y).comp (σ z') := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds hY hz'
    have e2 : σ (z * (z⁻¹ * Y * z')) = (σ z).comp (σ (z⁻¹ * Y * z')) :=
      Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds hz hM
    have e3 : z * (z⁻¹ * Y * z') = Y * z' := by
      rw [← mul_assoc, ← mul_assoc, hzi.2.1, one_mul]
    rw [e3] at e2
    have h2 := congrArg (fun T => T w) (e1.symm.trans e2)
    simpa using h2
  rw [h1]
  exact (⟨(σ z).toLinearMap, hiso⟩ : H →ₗᵢ[ℂ] H).inner_map_map w _

theorem gN_sandwich (hNI : NormInv) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {b : ℝ}
    (hb : 0 ≤ b) :
    B.gN (x⁻¹ * A * y) ^ (-b) ≤ (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by
  have hN := hNI k r
  have hxi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hx
  have hyi := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hy
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hxi.1 hA) hy
  have hm1 := (hN.2 _ hM).2
  have ha1 := (hN.2 _ hA).2
  have hx1 := (hN.2 _ hx).2
  have hy1 := (hN.2 _ hy).2
  have hyinv := (hN.2 _ hy).1
  have hAeq : x * (x⁻¹ * A * y) * y⁻¹ = A := by
    rw [show x * (x⁻¹ * A * y) * y⁻¹ = (x * x⁻¹) * A * (y * y⁻¹) by simp only [mul_assoc],
      hxi.2.1, hyi.2.1, one_mul, mul_one]
  have hle : B.gN A ≤ (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by
    calc B.gN A = B.gN (x * (x⁻¹ * A * y) * y⁻¹) := by rw [hAeq]
      _ ≤ B.gN (x * (x⁻¹ * A * y)) * B.gN y⁻¹ := hN.1 _ _
      _ ≤ B.gN x * B.gN (x⁻¹ * A * y) * B.gN y⁻¹ :=
          mul_le_mul_of_nonneg_right (hN.1 _ _) (by rw [hyinv]; linarith)
      _ = (B.gN x * B.gN y) * B.gN (x⁻¹ * A * y) := by rw [hyinv]; ring
  have hp : 0 < B.gN x * B.gN y := mul_pos (by linarith) (by linarith)
  have hmb : 0 < B.gN (x⁻¹ * A * y) ^ b := Real.rpow_pos_of_pos (by linarith) b
  have hab : 0 < B.gN A ^ b := Real.rpow_pos_of_pos (by linarith) b
  have key : B.gN A ^ b ≤ (B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b := by
    rw [← Real.mul_rpow hp.le (by linarith)]
    exact Real.rpow_le_rpow (by linarith) hle hb
  rw [Real.rpow_neg (show (0:ℝ) ≤ B.gN (x⁻¹ * A * y) by linarith),
    Real.rpow_neg (show (0:ℝ) ≤ B.gN A by linarith)]
  calc (B.gN (x⁻¹ * A * y) ^ b)⁻¹
        = (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * B.gN A ^ b * (B.gN A ^ b)⁻¹ := by
          exact (mul_inv_cancel_right₀ hab.ne' _).symm
    _ ≤ (B.gN (x⁻¹ * A * y) ^ b)⁻¹ * ((B.gN x * B.gN y) ^ b * B.gN (x⁻¹ * A * y) ^ b) *
          (B.gN A ^ b)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (inv_nonneg.2 hmb.le))
          (inv_nonneg.2 hab.le)
    _ = (B.gN x * B.gN y) ^ b * (B.gN A ^ b)⁻¹ := by
        rw [mul_comm ((B.gN x * B.gN y) ^ b) (B.gN (x⁻¹ * A * y) ^ b), inv_mul_cancel_left₀ hmb.ne']

end Formalism.FourierDecayAlt.P.S3dx4
