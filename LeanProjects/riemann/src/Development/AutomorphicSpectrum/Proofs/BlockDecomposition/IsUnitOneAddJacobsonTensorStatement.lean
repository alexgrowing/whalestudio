import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneAddJacobsonTensor
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_one_add_jacobson_tensor : ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing R] [Algebra O R] (x : O' ⊗[O] R), x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson → IsUnit (1 + x) := by
  first | exact @GlobalTheory.CompanionTheory.JacUnit.main | exact GlobalTheory.CompanionTheory.JacUnit.main | (intros; apply GlobalTheory.CompanionTheory.JacUnit.main <;> assumption)
