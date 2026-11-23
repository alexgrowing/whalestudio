import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCmData
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

namespace GlobalTheory.HCFinU

theorem cmData_starOf_unram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → @Formalism.BasicNotions.CMData F E _ _ _ _ (GlobalTheory.HCFinU.starOf σ hσ) _ := by
  intro F E _ _ _ _ _ σ hσ h hU
  letI := GlobalTheory.HCFinU.starOf σ hσ
  refine ⟨⟨h.2.1, fun φ a => h.2.2.2 φ a, fun P hP => ?_⟩, h.1, h.2.2.1,
    fun a => GlobalTheory.ThKUTr.cmConj_fixed h a⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThKUTr.exists_sub_notMem σ (GlobalTheory.ThKUTr.cmConj_ne_id h) hU P hP.ne_top
  exact ⟨θ, GlobalTheory.ThKUTr.intRestr σ θ, rfl, hθ⟩

end GlobalTheory.HCFinU
