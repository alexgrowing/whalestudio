import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedFieldStructure
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_field_structure : PositivityTheory.SiegelWeilFormula.Gunr.FixedK := by
  first | exact @GlobalTheory.CompanionTheory.FixedPointsCM.fixedK | exact GlobalTheory.CompanionTheory.FixedPointsCM.fixedK | (intros; apply GlobalTheory.CompanionTheory.FixedPointsCM.fixedK <;> assumption)
