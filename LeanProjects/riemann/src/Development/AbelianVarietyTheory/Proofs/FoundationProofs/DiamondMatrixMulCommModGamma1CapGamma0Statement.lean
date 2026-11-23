import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixMulCommModGamma1CapGamma0
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondMatrix_mul_comm_mod_gamma1CapGamma0 : ∀ (N l d d' : ℕ) (σ σ' : SL(2, ℤ)), IsDiam N l d σ → IsDiam N l d' σ' → ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ σ' * σ = g * (σ * σ') := by
  first | exact @GlobalTheory.KZ.isDiam_mul_comm_mod_Gam | exact GlobalTheory.KZ.isDiam_mul_comm_mod_Gam | (intros; apply GlobalTheory.KZ.isDiam_mul_comm_mod_Gam <;> assumption)
