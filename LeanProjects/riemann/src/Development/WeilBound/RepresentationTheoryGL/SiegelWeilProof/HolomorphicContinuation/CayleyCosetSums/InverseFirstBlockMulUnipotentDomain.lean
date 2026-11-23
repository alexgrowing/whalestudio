import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CapelliDeterminantRisingFactorial
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AnalyticAtInverseFirstBlock
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SecondCayleyBlockMulInverseCayley
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.ContDiffOnSecondCayleyBlockEntries
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperatorsAlt

noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem toBlocks₁₁_mul' (A B : M2 n) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ + A.toBlocks₁₂ * B.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks A, ← fromBlocks_toBlocks B, fromBlocks_multiply]
  simp

theorem inverse_first_block_eq_cayley (x : M2 n) : ub1 x = (2 * Complex.I) • (Cmi n * x⁻¹).toBlocks₁₁ := by
  rw [toBlocks₁₁_mul', Cmi, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, ub1]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul]
  congr 1
  · rw [show (2 * Complex.I * (-Complex.I / 2)) = 1 by ring_nf; simp [Complex.I_sq]]; simp
  · congr 1; ring

theorem inverse_second_block_eq_cayley (x : M2 n) : ub2 x = (2 * Complex.I) • (Cmi n * x⁻¹).toBlocks₂₁ := by
  rw [toBlocks₂₁_mul, Cmi, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, ub2]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul]
  have h1 : (2 * Complex.I * (Complex.I / 2)) = -1 := by ring_nf; simp [Complex.I_sq]
  rw [h1]
  simp only [neg_smul, one_smul]
  congr 1
  congr 1; ring

theorem cmi_mul_cm : Cmi n * Cm n = 1 := by
  rw [← cm_inv]; exact Cinv_mul_Cm

theorem mX_mul_mX_neg (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    mX 1 Q R 1 * mX 1 (-Q) (-R) 1 = 1 := by
  rw [mX, mX, cm_inv, show Cm n * fromBlocks 1 Q R 1 * Cmi n * (Cm n * fromBlocks 1 (-Q) (-R) 1 * Cmi n) =
    Cm n * (fromBlocks 1 Q R 1 * (Cmi n * Cm n) * fromBlocks 1 (-Q) (-R) 1) * Cmi n by
      simp only [Matrix.mul_assoc]]
  rw [cmi_mul_cm, Matrix.mul_one, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, hQR, hRQ, neg_zero, add_zero, add_neg_cancel,
    neg_add_cancel, zero_add]
  rw [show fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 1 = 1 from fromBlocks_one, Matrix.mul_one, cm_mul_cmi]

theorem mX_inv (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    (mX 1 Q R 1)⁻¹ = mX 1 (-Q) (-R) 1 := Matrix.inv_eq_right_inv (mX_mul_mX_neg Q R hQR hRQ)

theorem cmi_mX_neg (Q R : Matrix (Fin n) (Fin n) ℂ) :
    Cmi n * mX 1 (-Q) (-R) 1 = fromBlocks 1 (-Q) (-R) 1 * Cmi n := by
  rw [mX, cm_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, cmi_mul_cm, Matrix.one_mul]

theorem inverse_first_block_mul_unipotent (x : M2 n) (hx : IsUnit x.det) (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0) (hRQ : R * Q = 0) :
    ub1 (x * mX 1 Q R 1) = ub1 x - Q * ub2 x := by
  have hM : IsUnit (mX 1 Q R 1).det := by
    have h := mX_mul_mX_neg Q R hQR hRQ
    exact Matrix.isUnit_det_of_right_inverse h
  rw [inverse_first_block_eq_cayley, inverse_first_block_eq_cayley, inverse_second_block_eq_cayley, Matrix.mul_inv_rev, mX_inv Q R hQR hRQ, ← Matrix.mul_assoc, cmi_mX_neg,
    Matrix.mul_assoc, toBlocks₁₁_mul', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.one_mul]
  rw [Matrix.mul_smul, smul_add, neg_mul, smul_neg, sub_eq_add_neg]

theorem u_ub_rel (x : M2 n) (hx : IsUnit x.det) : u1 x * ub1 x + u2 x * ub2 x = 0 := by
  rw [inverse_first_block_eq_cayley, inverse_second_block_eq_cayley, ← mul_cm₂₁, ← mul_cm₂₂, Matrix.mul_smul, Matrix.mul_smul, ← smul_add, ← toBlocks₂₁_mul,
    show x * Cm n * (Cmi n * x⁻¹) = x * (Cm n * Cmi n) * x⁻¹ by simp only [Matrix.mul_assoc], cm_mul_cmi,
    Matrix.mul_one, Matrix.mul_nonsing_inv _ hx]
  rw [← fromBlocks_one, toBlocks_fromBlocks₂₁, smul_zero]

theorem inverse_first_block_mul_unipotent_domain (x : M2 n) (hx : x ∈ Dom n) (Q R : Matrix (Fin n) (Fin n) ℂ) (hQR : Q * R = 0)
    (hRQ : R * Q = 0) : ub1 (x * mX 1 Q R 1) = (1 + Q * wM x) * ub1 x := by
  rw [inverse_first_block_mul_unipotent x hx.1 Q R hQR hRQ]
  have h2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 hx.2.2.1
  have hrel := u_ub_rel x hx.1
  have e : ub2 x = -(wM x * ub1 x) := by
    have : u2 x * ub2 x = -(u1 x * ub1 x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hrel
    calc ub2 x = (u2 x)⁻¹ * (u2 x * ub2 x) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h2, Matrix.one_mul]
      _ = -(wM x * ub1 x) := by rw [this, Matrix.mul_neg, wM, Matrix.mul_assoc]
  rw [e, Matrix.mul_neg, sub_neg_eq_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]

theorem det_mX_one (Q R : Matrix (Fin n) (Fin n) ℂ) (hRQ : R * Q = 0) : (mX 1 Q R 1).det = 1 := by
  rw [mX, det_mul, det_mul, det_fromBlocks_one₁₁, hRQ, sub_zero, det_one, mul_one, ← det_mul, Matrix.mul_nonsing_inv]
  · exact det_one
  · exact Matrix.isUnit_det_of_right_inverse cm_mul_cmi

theorem embOn_mul_embOn_compl (j : ℕ) (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ) :
    embOn (blkA j) T * embOn (blkB j) S = 0 ∧ embOn (blkB j) S * embOn (blkA j) T = 0 := by
  constructor <;> ext a b <;> simp only [Matrix.mul_apply, Matrix.zero_apply, embOn] <;>
    refine Finset.sum_eq_zero fun k _ => ?_ <;> by_cases hk : k ∈ blkA j <;> simp_all [blkB]

end PositivityTheory.Rg.Sw.HSt
