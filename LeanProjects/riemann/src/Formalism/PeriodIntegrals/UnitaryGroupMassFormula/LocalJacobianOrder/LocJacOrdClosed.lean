import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianOrder.LocJacOrdOfSd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.SdNormHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale

noncomputable section

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain

theorem boxScale_holds : BoxScale := by
  intro F E _ _ _ _ _ v ι _ hfin μ _ x hx
  exact PI.UnitaryGroupMassFormula.LocJacTyp.boxScale v hfin μ x hx

theorem locJacOrd_closed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : PI.LocJacOrd.LocJacOrd (E := E) ψ v :=
  locJacOrd_of_sd ψ v (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sdNorm_holds (E := E) (ψ := ψ) (v := v)) boxScale_holds

end PI.LocJacOrd.W
