import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftReductionZeroOfMaximal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_reduction_zero_of_maximal : ∀ (A Q N : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [AddCommGroup N] [Module A N] [Module.Finite A N] [Module.Free A N] (b : Q →ₗ[A] N), Lift b → (∀ q, b q ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A N)) → b = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul | exact GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul | (intros; apply GlobalTheory.CompanionTheory.PerfVB.eq_zero_of_lift_of_mem_maximalIdeal_smul <;> assumption)
