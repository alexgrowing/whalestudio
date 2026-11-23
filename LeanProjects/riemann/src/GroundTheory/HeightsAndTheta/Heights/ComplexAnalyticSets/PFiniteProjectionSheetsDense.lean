import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetsDense
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionOffZerosDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem FiniteProjectionSheetsDense.proof (hP : IrreducibleGermPrimitiveForm.Statement)
    (hG : PrimitiveFormSheetedOffDiscriminant.Statement) (hD : FiniteProjectionOffZerosDense.Statement) :
    FiniteProjectionSheetsDense.Statement := by
  intro σ _ X w d A hX hI hiso hinj
  obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩ := hP σ X w d A hX hI hiso hinj
  obtain ⟨M, hM, hsh⟩ := hG σ X w d A hX hI hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  obtain ⟨N', hN', hcl⟩ := hD σ X w d A hX hI hiso hinj δ hδ hδ0
  refine ⟨interior M ∩ N', Filter.inter_mem (interior_mem_nhds.2 hM) hN', ?_⟩
  rintro z ⟨hzX, hzM, hzN⟩
  have hzc := hcl ⟨hzX, hzN⟩
  rw [mem_closure_iff_nhds] at hzc ⊢
  intro U hU
  obtain ⟨y, ⟨hyU, hyM⟩, hyX, hyδ⟩ :=
    hzc (U ∩ interior M) (Filter.inter_mem hU (isOpen_interior.mem_nhds hzM))
  exact ⟨y, hyU, hyX, hsh y ⟨hyX, interior_subset hyM⟩ hyδ⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
