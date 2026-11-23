import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

variable {F : Type} [Field F] [NumberField F]

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  exact PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  first
  | exact Valued.isOpen_valuationSubring _
  | exact Valued.isOpen_integer _

def Oint (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

theorem isOpen_Oint : IsOpen (Oint F) := by
  exact RestrictedProduct.isOpen_forall_mem fun v => isOpen_integers v

theorem algebraMap_int_mem_Oint (m : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) ∈ Oint F := by
  intro v
  exact coe_algebraMap_mem (𝓞 F) F v m

end ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact
