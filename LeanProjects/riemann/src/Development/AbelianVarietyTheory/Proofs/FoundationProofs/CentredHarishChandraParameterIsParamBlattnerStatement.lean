import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentredHarishChandraParameterIsParamBlattner
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centredHarishChandraParameter_isParam_blattner : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) → IsParam (hcParam n ap am) ∧ blattner (hcParam n ap am) = wtK n ap am ∧ ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
  first | exact @GlobalTheory.HarmonicParam.hcParam_isParam_blattner | exact GlobalTheory.HarmonicParam.hcParam_isParam_blattner | (intros; apply GlobalTheory.HarmonicParam.hcParam_isParam_blattner <;> assumption)
