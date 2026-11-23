import Formalism.HermitianCurvature.HermitianCurvatureProofs.GNMulRpow

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem cmHalfIntegralGenerator_mem_algebraicClosure {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hds : PI.UpqRep.IsDSHpk k r ε lam σ) (w0 : H) : w0 ∈ DDsp σ w0 := by
  have hone : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
    simp
  refine Submodule.subset_span ⟨1, hone, ?_⟩
  show σ 1 w0 = w0
  rw [(MatrixMultiplicationContinuity.sigma_facts hds).1]; rfl

theorem enorm_smulRight {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (a : E) (b : F) :
    ‖(innerSL ℂ a).smulRight b‖ₑ = ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, ENNReal.ofReal_mul (norm_nonneg _)]

theorem mt_cont : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := by
  first
    | exact continuous_id
    | fun_prop
    | continuity

theorem inner_bound (hNI : NormInv) {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : B.IsHaarOn (B.GV k r) μG)
    (hGc : ∀ᵐ x ∂μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) {C1 C2 a b : ℝ}
    (hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-a))
    (hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a)
    {P Q γi : Mx k r} (hP : P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hQ : Q ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hγ : γi ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ x, ‖e1 (P * Matrix.of x)‖ₑ * ‖e2 (Q * (γi * Matrix.of x))‖ₑ ∂μG ≤
      ENNReal.ofReal (|C1| * |C2|) * ‖B.gN (Q * γi * P⁻¹) ^ (-b)‖ₑ *
        ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG := by
  obtain ⟨hPi, hPP, -⟩ := MatrixMultiplicationContinuity.uh_inv hP
  set Y : Mx k r := Q * γi * P⁻¹ with hY
  have hYU : Y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul (DDSmoothness.uh_mul hQ hγ) hPi
  set F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ‖e1 (P * Matrix.of x)‖ₑ * ‖e2 (Q * (γi * Matrix.of x))‖ₑ with hF
  have hFm : Measurable F := by
    have c1 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => e1 (P * Matrix.of x)) :=
      he1.comp (continuous_const.matrix_mul mt_cont)
    have c2 : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => e2 (Q * (γi * Matrix.of x))) :=
      he2.comp (continuous_const.matrix_mul (continuous_const.matrix_mul mt_cont))
    exact c1.measurable.enorm.mul c2.measurable.enorm
  have hNI' := hNI k r
  calc ∫⁻ x, F x ∂μG = ∫⁻ x, F (Formalism.QuantumDeterminants.lmulM P⁻¹ x) ∂μG := (lint_left hG hPi hFm).symm
    _ ≤ ∫⁻ x, (ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ) * ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG := by
        apply lintegral_mono_ae
        filter_upwards [hGc] with x hx
        have e1x : P * Matrix.of (Formalism.QuantumDeterminants.lmulM P⁻¹ x) = Matrix.of x := by
          show P * (P⁻¹ * Matrix.of x) = Matrix.of x
          rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
        have e2x : Q * (γi * Matrix.of (Formalism.QuantumDeterminants.lmulM P⁻¹ x)) = Y * Matrix.of x := by
          show Q * (γi * (P⁻¹ * Matrix.of x)) = Q * γi * P⁻¹ * Matrix.of x
          simp only [Matrix.mul_assoc]
        simp only [hF]
        rw [e1x, e2x]
        have hYx : Y * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hYU hx
        have ht1 : 1 ≤ B.gN (Matrix.of x) := (hNI'.2 _ hx).2
        have htp : 0 < B.gN (Matrix.of x) := lt_of_lt_of_le one_pos ht1
        have hs1 : 1 ≤ B.gN (Y * Matrix.of x) := (hNI'.2 _ hYx).2
        have hYp : 0 ≤ B.gN Y ^ (-b) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
        have bnd1 : ‖e1 (Matrix.of x)‖ ≤ |C1| * B.gN (Matrix.of x) ^ (-a) :=
          (hb1 _ hx).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg htp.le _))
        have bnd2 : ‖e2 (Y * Matrix.of x)‖ ≤ |C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)) := by
          refine (hb2 _ hYx).trans ?_
          calc C2 * B.gN (Y * Matrix.of x) ^ (-a) ≤ |C2| * B.gN (Y * Matrix.of x) ^ (-a) :=
                mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
            _ ≤ |C2| * B.gN (Y * Matrix.of x) ^ (-b) :=
                mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)) (abs_nonneg _)
            _ ≤ |C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)) :=
                mul_le_mul_of_nonneg_left (gN_mul_rpow hNI hx hYU hb0) (abs_nonneg _)
        have key : |C1| * B.gN (Matrix.of x) ^ (-a) * (|C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b))) =
            (|C1| * |C2|) * B.gN Y ^ (-b) * B.gN (Matrix.of x) ^ (-(a - b)) := by
          have : B.gN (Matrix.of x) ^ (-a) * B.gN (Matrix.of x) ^ b = B.gN (Matrix.of x) ^ (-(a - b)) := by
            rw [← Real.rpow_add htp]; ring_nf
          calc |C1| * B.gN (Matrix.of x) ^ (-a) * (|C2| * (B.gN (Matrix.of x) ^ b * B.gN Y ^ (-b)))
              = (|C1| * |C2|) * B.gN Y ^ (-b) * (B.gN (Matrix.of x) ^ (-a) * B.gN (Matrix.of x) ^ b) := by ring
            _ = _ := by rw [this]
        have hxp : 0 ≤ B.gN (Matrix.of x) ^ (-(a - b)) := Real.rpow_nonneg htp.le _
        have hC : 0 ≤ |C1| * |C2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have L : ‖e1 (Matrix.of x)‖ₑ * ‖e2 (Y * Matrix.of x)‖ₑ =
            ENNReal.ofReal (‖e1 (Matrix.of x)‖ * ‖e2 (Y * Matrix.of x)‖) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
        have R : ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ * ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ =
            ENNReal.ofReal ((|C1| * |C2|) * B.gN Y ^ (-b) * B.gN (Matrix.of x) ^ (-(a - b))) := by
          rw [Real.enorm_eq_ofReal hYp, Real.enorm_eq_ofReal hxp, ENNReal.ofReal_mul (mul_nonneg hC hYp),
            ENNReal.ofReal_mul hC]
        rw [L, R]
        apply ENNReal.ofReal_le_ofReal
        rw [← key]
        exact mul_le_mul bnd1 bnd2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htp.le _))
    _ = ENNReal.ofReal (|C1| * |C2|) * ‖B.gN Y ^ (-b)‖ₑ * ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG :=
        lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top])

end Formalism.FourierDecayAlt.P.S3dx4
