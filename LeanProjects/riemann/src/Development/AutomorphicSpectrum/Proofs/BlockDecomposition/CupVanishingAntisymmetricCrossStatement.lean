import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupVanishingAntisymmetricCross
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_vanishing_antisymmetric_cross : LowSt → ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), Hopf F False → ∀ t : H1 F ⊗[R] H1 F, TensorProduct.lift (cup F) t = 0 → TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.hopf_cross_antisymm | exact GlobalTheory.CompanionTheory.WedgeOf.hopf_cross_antisymm | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.hopf_cross_antisymm <;> assumption)
