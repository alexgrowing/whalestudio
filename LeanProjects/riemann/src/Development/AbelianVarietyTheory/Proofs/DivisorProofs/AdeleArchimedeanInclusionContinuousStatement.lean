import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleArchimedeanInclusionContinuous
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_archimedean_inclusion_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], NumberField.IsTotallyReal F → ∀ Φ : AE F E ≃+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F), (∀ u : AdeleRing (𝓞 F) F, u.2 = 0 → Φ (algebraMap (AdeleRing (𝓞 F) F) (AE F E) u) = (fun w => InfinitePlace.Completion.extensionEmbedding w (u.1 w), 0)) → Continuous (fun c : InfinitePlace F → ℂ => Φ.symm (c, 0)) := by
  first | exact @GlobalTheory.DecCont.continuous_symm_inf | exact GlobalTheory.DecCont.continuous_symm_inf | (intros; apply GlobalTheory.DecCont.continuous_symm_inf <;> assumption)
