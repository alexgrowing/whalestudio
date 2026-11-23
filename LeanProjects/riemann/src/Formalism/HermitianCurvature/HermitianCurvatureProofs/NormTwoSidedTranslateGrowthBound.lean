import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableEnormComposition

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem norm_two_sided_translate_growth_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {x A y : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hA : A ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖e0 (x⁻¹ * A * y)‖ₑ ≤ ENNReal.ofReal (|C0| * (B.gN x * B.gN y) ^ b) * ‖B.gN A ^ (-b)‖ₑ := by
  have hxi := (MatrixMultiplicationContinuity.uh_inv hx).1
  have hM : x⁻¹ * A * y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hxi hA) hy
  have h1 : 1 ≤ B.gN (x⁻¹ * A * y) := ((hNI k r).2 _ hM).2
  have hAp : 0 ≤ B.gN A ^ (-b) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hxy : 0 ≤ (B.gN x * B.gN y) ^ b := Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
  rw [Real.enorm_eq_ofReal hAp, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hxy), ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  calc ‖e0 (x⁻¹ * A * y)‖ ≤ C0 * B.gN (x⁻¹ * A * y) ^ (-a) := hb0e _ hM
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-a) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C0| * B.gN (x⁻¹ * A * y) ^ (-b) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (abs_nonneg _)
    _ ≤ |C0| * ((B.gN x * B.gN y) ^ b * B.gN A ^ (-b)) :=
        mul_le_mul_of_nonneg_left (gN_sandwich hNI hx hA hy hb0) (abs_nonneg _)
    _ = |C0| * (B.gN x * B.gN y) ^ b * B.gN A ^ (-b) := by ring

theorem lam_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {γ : Mx k r} (hγ : γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hq : ∀ᵐ q ∂μq, Matrix.of q.1 * Matrix.of q.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    abelian₂ e0 γ μp μq x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ∫⁻ q, ‖B.gN ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) ^ (-b)‖ₑ ∂μq ∂μp := by
  unfold abelian₂
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hq] with q hqq
  have hQi := (MatrixMultiplicationContinuity.uh_inv hqq).1
  have hA : (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ ∈
      Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hpp hγ) hQi
  have e : (Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
      Matrix.of y = (Matrix.of x)⁻¹ * ((Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹) *
      Matrix.of y := by simp only [Matrix.mul_assoc]
  rw [e]
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hA hy

theorem lambda_integral_bound (hNI : NormInv) {e0 : Mx k r → ℂ} {C0 a b : ℝ}
    (hb0e : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e0 y‖ ≤ C0 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a) {μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)}
    (hp : ∀ᵐ p ∂μp, Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {x y : Formalism.QuantumDeterminants.Mt k r} (hx : Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hy : Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Lam1 e0 μp x y ≤ ENNReal.ofReal (|C0| * (B.gN (Matrix.of x) * B.gN (Matrix.of y)) ^ b) *
      ∫⁻ p, ‖B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)‖ₑ ∂μp := by
  unfold Lam1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hp] with p hpp
  exact norm_two_sided_translate_growth_bound hNI hb0e hb0 hba hx hpp hy

end Formalism.FourierDecayAlt.P.S3dx4
