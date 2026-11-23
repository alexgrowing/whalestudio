import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatTensorEmbedsTensorFractionFields
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_tensor_into_tensor_fractionFields : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U], ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧ ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by
  first | exact @GlobalTheory.flat_tensor_embeds_tensor_fractionFields | exact GlobalTheory.flat_tensor_embeds_tensor_fractionFields | (intros; apply GlobalTheory.flat_tensor_embeds_tensor_fractionFields <;> assumption)
