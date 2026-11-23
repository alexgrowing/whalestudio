import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizeInequalitiesNoLevelPrimeColumnNormParameters
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeInequalitiesNoLevelPrime_columnNormParameters : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), SizeRowsS CY (numDatumOfParameters D L) (codeRec L u) := by
  first | exact @GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec | exact GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec | (intros; apply GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec <;> assumption)
