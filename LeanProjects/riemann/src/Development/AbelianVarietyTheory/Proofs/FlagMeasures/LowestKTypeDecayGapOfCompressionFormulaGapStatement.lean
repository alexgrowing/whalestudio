import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_decayGap_of_compressionFormulaGap : FormulaGap → DecGap := by
  first | exact @GlobalTheory.DecGapBound.decGap_of_formulaGap | exact GlobalTheory.DecGapBound.decGap_of_formulaGap | (intros; apply GlobalTheory.DecGapBound.decGap_of_formulaGap <;> assumption)
