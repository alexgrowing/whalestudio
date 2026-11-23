import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallLiftBaseChangeLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_lift_base_change_local : ∀ (R P₀ P₁ P₂ A : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] [CommRing A] [IsLocalRing A] [Algebra R A] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂), a₁ ∘ₗ a₀ = 0 → SmallLift a₀ a₁ → Lift (a₁.baseChange A) := by
  first | exact @GlobalTheory.CompanionTheory.PerfVB.lift_of_smallLift | exact GlobalTheory.CompanionTheory.PerfVB.lift_of_smallLift | (intros; apply GlobalTheory.CompanionTheory.PerfVB.lift_of_smallLift <;> assumption)
