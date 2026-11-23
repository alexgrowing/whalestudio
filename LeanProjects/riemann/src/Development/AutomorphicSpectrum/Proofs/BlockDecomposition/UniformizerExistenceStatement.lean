import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistence
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_existence : PositivityTheory.SiegelWeilFormula.Gunr.UnifEx := by
  first | exact @GlobalTheory.CompanionTheory.LocalUnif.unifEx | exact GlobalTheory.CompanionTheory.LocalUnif.unifEx | (intros; apply GlobalTheory.CompanionTheory.LocalUnif.unifEx <;> assumption)
