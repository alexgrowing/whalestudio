import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishingOfGradedNoetherian
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_vanishing_of_graded_noetherian : GradedNoeth → UniformVanishing := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.uniformVanishing | exact GlobalTheory.CompanionTheory.GE.UV.uniformVanishing | (intros; apply GlobalTheory.CompanionTheory.GE.UV.uniformVanishing <;> assumption)
