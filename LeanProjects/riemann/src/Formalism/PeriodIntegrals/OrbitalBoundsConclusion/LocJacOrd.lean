import Mathlib
import Formalism.PeriodIntegrals.LocJacOrd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianOrder.LocJacOrdClosed

theorem locJacOrd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    PI.LocJacOrd.LocJacOrd (E := E) ψ v :=
  PI.LocJacOrd.W.locJacOrd_closed ψ v
