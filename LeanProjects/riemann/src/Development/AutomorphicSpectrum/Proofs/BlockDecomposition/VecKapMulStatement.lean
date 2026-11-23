import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMul
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_term_identity : Term := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTerm.term | exact GlobalTheory.CompanionTheory.RgEisTerm.term | (intros; apply GlobalTheory.CompanionTheory.RgEisTerm.term <;> assumption)
