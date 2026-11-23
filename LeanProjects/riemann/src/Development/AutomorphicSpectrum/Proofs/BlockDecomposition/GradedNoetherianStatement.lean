import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedNoetherian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_noetherian : GradedNoeth := by
  first | exact @GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth | exact GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth | (intros; apply GlobalTheory.CompanionTheory.GE.GNoeth.gradedNoeth <;> assumption)
