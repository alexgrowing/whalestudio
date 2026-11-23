import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.SdNormHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ExpProductSquareInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.CentreVolume
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.DeepCongruenceVolume
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ParabolicVolume

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain

theorem locJacTyp_closed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    PI.LocJacTyp.LocJacTyp σ ψ v :=
  locJacTyp_of σ ψ v (Sd.sdNorm_holds (E := E) (ψ := ψ) (v := v)) (centre_volume σ v) (unipotent_volume σ v)
    (parabolic_volume σ v) (quadraticDifferenceArith v)

end PI.UnitaryGroupMassFormula.LocJacTyp
