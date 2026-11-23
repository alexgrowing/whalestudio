import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HarmonicHighestWeightEqLowestKTypeHighestWeight
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (μ : Ix p q → ℚ) (P : Pol p q n 0), IsHW (fockAct1 p q n 0) μ P → P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) → KilledByLower (fockAct1 p q n 0) P → μ = wtK n ap am := by
  first | exact @GlobalTheory.HarmonicShape.weight_eq_wtK | exact GlobalTheory.HarmonicShape.weight_eq_wtK | (intros; apply GlobalTheory.HarmonicShape.weight_eq_wtK <;> assumption)
