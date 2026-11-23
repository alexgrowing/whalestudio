import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockUnitriangularFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_block_unitriangular_flag : ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → g i j = (1 : Mat k r) i j := by
  first | exact @GlobalTheory.CellDens.nset_block_unitriangular | exact GlobalTheory.CellDens.nset_block_unitriangular | (intros; apply GlobalTheory.CellDens.nset_block_unitriangular <;> assumption)
