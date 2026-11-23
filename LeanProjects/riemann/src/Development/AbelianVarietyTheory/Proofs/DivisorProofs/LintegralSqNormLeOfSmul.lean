import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativePreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeEquivarianceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnitHeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevUniformBoundPeriodicStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section
namespace GlobalTheory.ThetaDecay

variable {F : Type} [Field F] [NumberField F]

theorem evI_algebraMap_eq (x : F) : evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

open scoped Classical in
theorem sum_places_le : ∃ c : ℝ, ∀ ξ : F, ∑ w : InfinitePlace F, w ξ ≤ c * ‖evI F (algebraMap F (AF F) ξ)‖ := by
  refine ⟨Fintype.card (InfinitePlace F), fun ξ => ?_⟩
  rw [evI_algebraMap_eq]
  have h : ∀ w : InfinitePlace F, w ξ ≤ ‖mixedEmbedding F ξ‖ := by
    intro w
    rw [← mixedEmbedding.normAtPlace_apply w ξ]
    by_cases hw : w.IsReal
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
      exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
      exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
  calc ∑ w : InfinitePlace F, w ξ ≤ ∑ _w : InfinitePlace F, ‖mixedEmbedding F ξ‖ := Finset.sum_le_sum fun w _ => h w
    _ = _ := by simp

end GlobalTheory.ThetaDecay
end

noncomputable section
namespace GlobalTheory.ThetaDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

end GlobalTheory.ThetaDecay

namespace GlobalTheory.ThetaDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ThetaDecay
end

noncomputable section
namespace GlobalTheory.ThetaDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ThetaDecay
end

noncomputable section
namespace GlobalTheory.ThetaDecay

end GlobalTheory.ThetaDecay
end
