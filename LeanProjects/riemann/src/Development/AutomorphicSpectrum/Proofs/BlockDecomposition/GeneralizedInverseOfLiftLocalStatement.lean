import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedInverseOfLiftLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftReductionZeroOfMaximalStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalized_inverse_of_lift_local : ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [Module.Free A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N), Lift b → ∃ s : N →ₗ[A] Q, b ∘ₗ s ∘ₗ b = b := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift | exact GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift | (intros; apply GlobalTheory.CompanionTheory.PerfVB.exists_generalised_inverse_of_lift <;> assumption)
