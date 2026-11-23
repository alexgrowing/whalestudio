import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_generation_of_vanishing : GradedNoeth → UniformVanishing → UniformGen := by
  first | exact @GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth | exact GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth | (intros; apply GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth <;> assumption)
