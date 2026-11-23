import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitEqSumSlash
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash : ∀ (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q), GlobalTheory.Hk.uOp q f = ∑ j ∈ Finset.range q, f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  first | exact @GlobalTheory.Hk.uOp_eq_sum_slash | exact GlobalTheory.Hk.uOp_eq_sum_slash | (intros; apply GlobalTheory.Hk.uOp_eq_sum_slash <;> assumption)
