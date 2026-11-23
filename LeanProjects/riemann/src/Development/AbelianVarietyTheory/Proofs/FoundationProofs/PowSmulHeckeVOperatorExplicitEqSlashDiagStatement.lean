import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowSmulHeckeVOperatorExplicitEqSlashDiag
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_smul_heckeVOperatorExplicit_eq_slash_diag : ∀ (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q), (q : ℂ) ^ (k - 1) • GlobalTheory.Hk.vOp q f = f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  first | exact @GlobalTheory.Hk.smul_vOp_eq_slash | exact GlobalTheory.Hk.smul_vOp_eq_slash | (intros; apply GlobalTheory.Hk.smul_vOp_eq_slash <;> assumption)
