import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuOne
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuOneDet
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuOneCoeff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial FlagIntMuOne

theorem FlagIntMuOne.proof : FlagIntMuOne.Statement := by
  intro N j hjN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjN
  rw [Nat.add_sub_cancel_left, flagInt_unit_eq]
  simp_rw [coeff_muPow_rhoBlock]
  have hdet : (flagMat j m).det =
      ∑ σ : Equiv.Perm (Fin (j + m)), ((Equiv.Perm.sign σ : ℤ) : ℚ) * ∏ i, flagMat j m i (σ i) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  calc ∑ σ : Equiv.Perm (Fin (j + m)),
        ((Equiv.Perm.sign σ : ℤ) : ℚ) * (((j * m).factorial : ℚ) * ∏ i, flagMat j m i (σ i))
      = ((j * m).factorial : ℚ) * (flagMat j m).det := by
        rw [hdet, Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring
    _ = (-1) ^ (j * m) * grassDeg j m := by
        rw [det_flagMat, prod_factorial_div_comm, grassDeg]
        ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
