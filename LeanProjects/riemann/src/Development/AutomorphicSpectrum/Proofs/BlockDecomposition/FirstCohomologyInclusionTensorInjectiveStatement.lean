import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyInclusionTensorInjective
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_cohomology_inclusion_tensor_injective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), H1CommutesBaseChange F → ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective ((iotaQ F).lTensor M) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | exact GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.iotaQ_lTensor_injective <;> assumption)
