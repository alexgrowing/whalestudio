import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.InertOfNoEmb

theorem exists_isInertAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ Formalism.UG.IsInertAt F E v w := by
  intro F E _ _ _ _ _ σ hc hu v hv
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v := by
    intro P _
    rw [Ideal.ramificationIdx_eq_one_iff]
    infer_instance
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | ⟨w, hw⟩
  · obtain ⟨P, Q, hne, hP, hQ⟩ := hs
    obtain ⟨τ, _⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hc ⟨P, Q, hne, hP, hQ⟩ (w := P)
      (HeightOneSpectrum.ext hP)
    exact hv.elim τ
  · exact ⟨w, (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl, hw⟩

end GlobalTheory.InertOfNoEmb
