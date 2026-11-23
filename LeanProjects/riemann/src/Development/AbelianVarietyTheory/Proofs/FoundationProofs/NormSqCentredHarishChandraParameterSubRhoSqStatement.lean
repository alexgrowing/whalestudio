import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSqCentredHarishChandraParameterSubRhoSq
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normSq_centredHarishChandraParameter_sub_rhoSq : ∀ (p q n : ℕ) (ap : Fin p → ℕ) (am : Fin q → ℕ), normSq (hcParam n ap am) - rhoSq (p + q) = (∑ a, wtK n ap am a ^ 2 + ∑ i : Fin p, wtK n ap am (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, wtK n ap am (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) := by
  first | exact @GlobalTheory.normSq_hcParam_sub_rhoSq | exact GlobalTheory.normSq_hcParam_sub_rhoSq | (intros; apply GlobalTheory.normSq_hcParam_sub_rhoSq <;> assumption)
