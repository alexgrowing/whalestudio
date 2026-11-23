import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocSec
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem JJ_inv : (JJ n)⁻¹ = -JJ n := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.neg_mul, JJ_mul_JJ, neg_neg]

theorem JJ_conjT : (JJ n)ᴴ = -JJ n := by
  simp [JJ, fromBlocks_conjTranspose, fromBlocks_neg]

theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  simp [sig, JJ_inv]

theorem sig_sig (X : M2 n) : sig (sig X) = X := by
  have h1 : ∀ B : M2 n, JJ n * (JJ n * B) = -B := by
    intro B
    rw [← Matrix.mul_assoc, JJ_mul_JJ, Matrix.neg_mul, Matrix.one_mul]
  rw [sig_eq, sig_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, JJ_conjT, Matrix.mul_assoc,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg, h1, JJ_mul_JJ, Matrix.mul_one]

theorem sig_add (X Y : M2 n) : sig (X + Y) = sig X + sig Y := by
  simp [sig_eq, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem sig_smul (c : ℂ) (X : M2 n) : sig (c • X) = (starRingEnd ℂ c) • sig X := by
  simp only [sig_eq, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Complex.star_def]

theorem sig_sub (X Y : M2 n) : sig (X - Y) = sig X - sig Y := by
  simp [sig_eq, Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

def Z1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def Z2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

theorem conj_real_part_fixed (Z : M2 n) : sig (Z1 Z) = Z1 Z := by
  have hc : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  rw [Z1, sig_smul, sig_add, sig_sig, hc, add_comm]

theorem conj_imaginary_part_fixed (Z : M2 n) : sig (Z2 Z) = Z2 Z := by
  have hc : starRingEnd ℂ (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp only [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    field_simp
  rw [Z2, sig_smul, sig_sub, sig_sig, hc, neg_smul, ← smul_neg, neg_sub]

theorem real_add_imaginary_part (Z : M2 n) : Z1 Z + Complex.I • Z2 Z = Z := by
  have hc : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  simp only [Z1, Z2, smul_smul, hc]
  module

theorem inG_cE {A : M2 n} (hA : sig A = A) (s : ℝ) : InG (II.cE A s) := by
  have hJJ := JJ_mul_JJ (n := n)
  let U : (M2 n)ˣ := ⟨JJ n, -JJ n, by rw [Matrix.mul_neg, hJJ, neg_neg],
    by rw [Matrix.neg_mul, hJJ, neg_neg]⟩
  have hAh : Aᴴ = JJ n * A * JJ n := by
    have h := hA
    rw [sig_eq] at h
    calc Aᴴ = (JJ n * JJ n) * Aᴴ * (JJ n * JJ n) := by
          rw [hJJ, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]
      _ = JJ n * (JJ n * Aᴴ * JJ n) * JJ n := by simp only [Matrix.mul_assoc]
      _ = JJ n * A * JJ n := by rw [h]
  have hB : (s • A)ᴴ = (U : M2 n) * (-(s • A)) * ((U⁻¹ : (M2 n)ˣ) : M2 n) := by
    show (s • A)ᴴ = JJ n * (-(s • A)) * (-JJ n)
    rw [conjTranspose_smul, star_trivial, hAh]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_smul, Matrix.smul_mul]
  unfold InG II.cE
  rw [← Matrix.exp_conjTranspose, hB, Matrix.exp_units_conj]
  show JJ n * NormedSpace.exp (-(s • A)) * (-JJ n) * JJ n * NormedSpace.exp (s • A) = JJ n
  rw [Matrix.mul_assoc (JJ n * _) (-JJ n) (JJ n), Matrix.neg_mul, hJJ, neg_neg, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute (-(s • A)) (s • A) ((Commute.refl (s • A)).neg_left),
    neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

end PositivityTheory.Rg.Sw.HSt.CR
