import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianOrder.SecondCountableFv

noncomputable section

namespace PI.LocJacOrd.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacOrd

theorem locJacOrd_of_sd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (h0 : SdNormO (E := E) ψ v)
    (hB : BoxScale) : LocJacOrd (E := E) ψ v :=
  locJacOrd_of ψ v h0 (volZZO_of v hB absMul_holds) (volUO_of v hB absMul_holds)
    (volPO_of v hB absMul_holds) (arithO_holds v)

end PI.LocJacOrd.W
