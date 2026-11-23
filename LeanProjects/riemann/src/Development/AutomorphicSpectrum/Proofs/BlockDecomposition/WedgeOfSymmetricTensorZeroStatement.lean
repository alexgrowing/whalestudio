import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfSymmetricTensorZero
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_of_symmetric_tensor_zero : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V] (t : V ⊗[R] V), t - TensorProduct.comm R V V t = 0 → wedgeT (R := R) V t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm | exact GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm <;> assumption)
