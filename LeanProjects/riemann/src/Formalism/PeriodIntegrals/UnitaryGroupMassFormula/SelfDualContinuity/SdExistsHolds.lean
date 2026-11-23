import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.ContinuousReTupSymm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExInst

noncomputable section

namespace PI.SelfDualBridge.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem sdExists_holds {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ) (ι : Type) [Fintype ι] :
    PI.SelfDualBridge.SdExists σ J ψ v a ι :=
  sdExists_of_sdEx (PI.OmFibreUniq.W.SdInst.sdEx_of_psiNT PI.OmFibreUniq.W.Sd.additive_character_nontrivial)
    σ J ψ v a ι

end PI.SelfDualBridge.W
