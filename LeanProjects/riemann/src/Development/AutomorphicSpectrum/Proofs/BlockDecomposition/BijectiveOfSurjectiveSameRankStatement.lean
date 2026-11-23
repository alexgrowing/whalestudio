import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveOfSurjectiveSameRank
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_of_surjective_same_rank : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (n : ℕ), VB R A n → VB R B n → ∀ f : A →ₗ[R] B, Function.Surjective f → Function.Bijective f := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB | exact GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.bijective_of_surjective_of_VB <;> assumption)
