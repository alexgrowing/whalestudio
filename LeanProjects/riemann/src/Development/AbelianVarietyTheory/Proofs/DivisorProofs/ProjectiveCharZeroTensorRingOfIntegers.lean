import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem isReduced_charZero_tensor_ringOfIntegers (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] : IsReduced (k ⊗[ℤ] 𝓞 F) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  haveI : IsReduced (k ⊗[ℤ] F) := Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[ℤ] F)
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℤ k) (IsScalarTower.toAlgHom ℤ (𝓞 F) F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective _ hinj

instance isSemisimpleRing_charZero_tensor_ringOfIntegers (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] : IsSemisimpleRing (k ⊗[ℤ] 𝓞 F) := by
  haveI := isReduced_charZero_tensor_ringOfIntegers F k
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 F) := IsArtinianRing.of_finite k _
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem projective_charZero_tensor_ringOfIntegers : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] 𝓞 F) M], Module.Projective (k ⊗[ℤ] 𝓞 F) M := by
  intro F _ _ k _ _ M _ _
  exact Module.projective_of_isSemisimpleRing _ _

end GlobalTheory
