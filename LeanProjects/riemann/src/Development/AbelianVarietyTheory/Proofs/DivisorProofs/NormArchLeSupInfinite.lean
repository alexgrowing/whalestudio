import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ThetaDecay

theorem archAt_eq_ext (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (a : AF F) :
    archAt F w a = InfinitePlace.Completion.extensionEmbedding w (a.1 w) := rfl

theorem evI_fst (F : Type) [Field F] [NumberField F] (a : AF F) (v : {w : InfinitePlace F // w.IsReal}) :
    ((evI F a).1 v : ℂ) = archAt F v.1 a := by
  rw [archAt_eq_ext, evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

theorem evI_snd (F : Type) [Field F] [NumberField F] (a : AF F) (v : {w : InfinitePlace F // w.IsComplex}) :
    (evI F a).2 v = archAt F v.1 a := by
  rw [archAt_eq_ext, evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]

theorem norm_evI_sup : ∀ (F : Type) [Field F] [NumberField F] (a : AF F),
    (∀ w, ‖archAt F w a‖ ≤ ‖evI F a‖) ∧ ∀ B : ℝ, 0 ≤ B → (∀ w, ‖archAt F w a‖ ≤ B) → ‖evI F a‖ ≤ B := by
  intro F _ _ a
  refine ⟨fun w => ?_, fun B hB h => ?_⟩
  · rcases w.isReal_or_isComplex with hw | hw
    · have e := evI_fst F a ⟨w, hw⟩
      have : ‖archAt F w a‖ = ‖(evI F a).1 ⟨w, hw⟩‖ := by
        rw [← e, Complex.norm_real]
      rw [this]
      exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
    · have e := evI_snd F a ⟨w, hw⟩
      have : ‖archAt F w a‖ = ‖(evI F a).2 ⟨w, hw⟩‖ := by rw [e]
      rw [this]
      exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
  · rw [Prod.norm_def, max_le_iff]
    refine ⟨(pi_norm_le_iff_of_nonneg hB).2 fun v => ?_, (pi_norm_le_iff_of_nonneg hB).2 fun v => ?_⟩
    · have := h v.1
      rw [← evI_fst F a v, Complex.norm_real] at this
      exact this
    · have := h v.1
      rw [← evI_snd F a v] at this
      exact this

end GlobalTheory.ThetaDecay
