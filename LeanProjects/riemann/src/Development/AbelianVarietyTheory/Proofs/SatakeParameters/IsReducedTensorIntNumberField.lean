import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedNormOfReducedNorm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryConjugateLocal
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem isReduced_tensor_int_numberField (F K : Type) [Field F] [NumberField F] [Field K] :
    IsReduced (K ⊗[ℤ] F) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  haveI : Algebra.FormallyUnramified K (K ⊗[ℤ] F) := inferInstance
  haveI : Algebra.EssFiniteType K (K ⊗[ℤ] F) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[ℤ] F)

end GlobalTheory
