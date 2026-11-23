import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

namespace GlobalTheory.ThK.LemF.QuotInv.Facts

theorem vecAt_skewAt_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (m : ℕ) (v : Pl F),
    (LocallyCompactSpace (vecAt F E m (evFin F v)) ∧ SecondCountableTopology (vecAt F E m (evFin F v)) ∧
      T2Space (vecAt F E m (evFin F v)) ∧ BorelSpace (vecAt F E m (evFin F v))) ∧
    (LocallyCompactSpace (skewAt σ (evFin F v)) ∧ SecondCountableTopology (skewAt σ (evFin F v)) ∧
      T2Space (skewAt σ (evFin F v)) ∧ BorelSpace (skewAt σ (evFin F v))) := by
  intro F E _ _ _ _ _ σ m v
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hV : IsClosed (vecAt F E m (evFin F v) : Set (Fin m → AE F E)) := by
    change IsClosed {w : Fin m → AE F E | ∀ u, evFin F v u = 0 → u • w = 0}
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun u => isClosed_iInter fun _ =>
      isClosed_eq (continuous_id.const_smul u) continuous_const
  have hS : IsClosed (skewAt σ (evFin F v) : Set (AE F E)) := by
    have hc : Continuous (cA σ : AE F E → AE F E) := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
    change IsClosed ({c : AE F E | ∀ u, evFin F v u = 0 → u • c = 0} ∩ {c | cA σ c = -c})
    refine IsClosed.inter ?_ (isClosed_eq hc continuous_neg)
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun u => isClosed_iInter fun _ =>
      isClosed_eq (continuous_id.const_smul u) continuous_const
  haveI : BorelSpace (AE F E) := inferInstance
  haveI : BorelSpace (Fin m → AE F E) := Pi.borelSpace
  haveI : SecondCountableTopology (Fin m → AE F E) := inferInstance
  refine ⟨⟨hV.isClosedEmbedding_subtypeVal.locallyCompactSpace,
      hV.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance, Subtype.borelSpace _⟩,
    ⟨hS.isClosedEmbedding_subtypeVal.locallyCompactSpace,
      hS.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance, Subtype.borelSpace _⟩⟩

end GlobalTheory.ThK.LemF.QuotInv.Facts
