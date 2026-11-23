import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatQuotientOfUniversallyInjective
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_quotient_of_universally_injective : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [Module.Flat R B] (f : A →ₗ[R] B), (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (f.lTensor M)) → Module.Flat R (B ⧸ LinearMap.range f) := by
  first | exact @GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | exact GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective | (intros; apply GlobalTheory.CompanionTheory.FlatCoker.flat_quotient_range_of_lTensor_injective <;> assumption)
