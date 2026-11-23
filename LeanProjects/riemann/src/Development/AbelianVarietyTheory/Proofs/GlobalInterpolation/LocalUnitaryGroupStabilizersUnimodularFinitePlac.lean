import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

namespace GlobalTheory.LocalUnitaryUnimod

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem unimodularOver_adicCompletion :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
      IsHermND σ J → ∀ v : HeightOneSpectrum (𝓞 F), UnimodularOver (Fv F v) σ J := by
  intro F E _ _ _ _ _ σ hσ M J hJ v
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  exact GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (Fv F v) hσ hJ

end GlobalTheory.LocalUnitaryUnimod
