import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CompatibleThetaRestrictions
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ResFirstCont

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem continuous_res_left : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ x, Continuous fun m : GA D V => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) x := by
  intro D V V' W r C B ψ χS χT ω hω μ 𝓨 h𝓨 f hf x
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓨.2.2]; exact ENNReal.one_lt_top⟩
  have hy : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B x := by
    unfold isoPart
    exact (continuous_id.matrix_mul continuous_const).add continuous_const
  refine continuous_iff_continuousAt.2 fun m₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds m₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f hf (K ×ˢ {1})
    (hK.prod isCompact_singleton)
  unfold res
  refine continuousAt_of_dominated (bound := fun _ => c) ?_ ?_ (integrable_const c) ?_
  · exact Filter.Eventually.of_forall fun m =>
      ((hω.om_pres (m, 1) f hf).cont.comp hy).aestronglyMeasurable
  · filter_upwards [hKn] with m hm
    exact Filter.Eventually.of_forall fun y => hc (m, 1) ⟨hm, rfl⟩ _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact ((hω.om_cont f hf _).comp (Continuous.prodMk_left 1)).continuousAt

end GlobalTheory.ResFirstCont

end
