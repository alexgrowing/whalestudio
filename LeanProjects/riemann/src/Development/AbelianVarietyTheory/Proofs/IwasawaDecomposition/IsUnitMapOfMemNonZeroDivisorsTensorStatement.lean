import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitMapOfMemNonZeroDivisorsTensor
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_map_of_mem_nonZeroDivisors_tensor' : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), Function.Injective φ → (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ s ∈ nonZeroDivisors (U ⊗[T] C), IsUnit (φ s) := by
  first | exact @GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor | exact GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor | (intros; apply GlobalTheory.isUnit_map_of_mem_nonZeroDivisors_tensor <;> assumption)
