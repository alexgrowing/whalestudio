import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramMinorDetTriangularMulStatement

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

theorem gram_nonneg_vmul (k r : ℕ) (g : Mat k r) (a : Fin (r + 1)) : 0 ≤ gram k r g a := by
  unfold gram
  have h := ((Matrix.posSemidef_conjTranspose_mul_self (g * frame k r)).submatrix
    (Fin.castLE (Nat.succ_le_of_lt a.isLt))).det_nonneg
  exact (Complex.nonneg_iff.mp h).1

theorem gram_unitary_mul (k r : ℕ) (κ g : Mat k r) (hκ : κᴴ * κ = 1) (a : Fin (r + 1)) :
    gram k r (κ * g) a = gram k r g a := by
  have h : (κ * g * frame k r)ᴴ * (κ * g * frame k r) = (g * frame k r)ᴴ * (g * frame k r) := by
    rw [Matrix.mul_assoc κ g, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]
  unfold gram
  rw [h]

theorem gram_mul_flag (k r : ℕ) (hk : 1 ≤ k) (g p : Mat k r) (hp : p ∈ Pset k r)
    (a : Fin (r + 1)) : gram k r (g * p) a = gram k r g a * gram k r p a := by
  obtain ⟨-, u, hu, hpu⟩ := hp
  have hF := (GlobalTheory.T.frame_isotropic_orthonormal k r hk).1
  have h1 := GlobalTheory.T.gram_minor_det_triangular_mul _ _ (g * frame k r) u _ (Nat.succ_le_of_lt a.isLt) hu
  have h2 := GlobalTheory.T.gram_minor_det_triangular_mul _ _ (frame k r) u _ (Nat.succ_le_of_lt a.isLt) hu
  have e1 : g * p * frame k r = g * frame k r * u := by
    rw [Matrix.mul_assoc, hpu, Matrix.mul_assoc]
  rw [hF, Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one, mul_one] at h2
  unfold gram
  rw [e1, hpu, h1, h2, Complex.re_ofReal_mul, Complex.ofReal_re, mul_comm]

theorem vHalf_left_inv_and_mul : ∀ k r : ℕ, 1 ≤ k →
    (∀ κ ∈ Kset k r, ∀ g : Mat k r, vHalf k r (κ * g) = vHalf k r g) ∧
    ∀ g ∈ GV k r, ∀ p ∈ Pset k r, vHalf k r (g * p) = vHalf k r g * vHalf k r p := by
  intro k r hk
  refine ⟨fun κ hκ g => ?_, fun g _ p hp => ?_⟩
  · unfold vHalf
    simp only [gram_unitary_mul k r κ g hκ.2]
  · unfold vHalf
    simp only [gram_mul_flag k r hk g p hp, mul_inv, Finset.prod_mul_distrib]
    rw [Real.mul_rpow (gram_nonneg_vmul k r g _) (gram_nonneg_vmul k r p _)]
    ring

end GlobalTheory.HCXi
