import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossProductKernelQuotientVanishing
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cross_product_kernel_quotient_vanishing : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] [Finite C] [Quiver.IsThin C] (F : C ⥤ CommAlgCat.{0} R) (t : H1 F ⊗[R] H1 F), TensorProduct.lift (crossB F) t = 0 → TensorProduct.map (iotaQ F) (iotaQ F) t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero | exact GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.Shuffle.map_iotaQ_eq_zero <;> assumption)
