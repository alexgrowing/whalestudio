import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_value_formula : Equi → CountBd → MeanVal := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | exact GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd <;> assumption)
