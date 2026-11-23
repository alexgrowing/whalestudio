import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolutionSmoothL2_of_def : ConvolutionSmoothL2 := by
  first | exact @GlobalTheory.SmoothGrowth.convolutionSmoothL2 | exact GlobalTheory.SmoothGrowth.convolutionSmoothL2 | (intros; apply GlobalTheory.SmoothGrowth.convolutionSmoothL2 <;> assumption)
