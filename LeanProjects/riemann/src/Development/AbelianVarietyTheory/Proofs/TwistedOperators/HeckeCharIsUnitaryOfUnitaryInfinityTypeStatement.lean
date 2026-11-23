import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityType
import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  first | exact @GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | exact GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | (intros; apply GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf <;> assumption)
