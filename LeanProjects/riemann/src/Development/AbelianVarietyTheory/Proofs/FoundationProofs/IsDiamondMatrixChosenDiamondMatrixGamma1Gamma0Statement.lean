import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixChosenDiamondMatrixGamma1Gamma0
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiamondMatrix_chosenDiamondMatrixGamma1Gamma0 : ∀ (N l d : ℕ), l.Prime → 0 < N → Nat.Coprime N l → Nat.Coprime d N → IsDiam N l d (sgD N l d) := by
  first | exact @GlobalTheory.KZ.isDiam_sgD_of_prime | exact GlobalTheory.KZ.isDiam_sgD_of_prime | (intros; apply GlobalTheory.KZ.isDiam_sgD_of_prime <;> assumption)
