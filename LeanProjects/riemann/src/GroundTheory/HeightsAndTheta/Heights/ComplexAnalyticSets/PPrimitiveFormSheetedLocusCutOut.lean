import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormFullRootFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedLocusCutOut.proof (hfac : PrimitiveFormFullRootFactor.Statement)
    (hiff : PrimitiveFormSheetedIffRootFull.Statement) : PrimitiveFormSheetedLocusCutOut.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨W, B, C, E, hW, hwW, hB, hwB, han, hCE, hroot⟩ :=
    hfac σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  have hBn : ∀ᶠ z in 𝓝 w, A z ∈ B := A.continuous.continuousAt.preimage_mem_nhds (hB.mem_nhds hwB)
  have hc : ∀ F : (Fin d → ℂ) → ℂ → ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F u.1 u.2) (A w, ℓ w) →
      AnalyticAt ℂ (fun z => F (A z) (ℓ z)) w := fun F hF =>
    (show AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F u.1 u.2) ((A.prod ℓ) w) from hF).comp
      ((A.prod ℓ).analyticAt w)
  refine ⟨fun z => C (A z) (ℓ z), fun z => E (A z) (ℓ z), hc C (han _ hwB _).1, hc E (han _ hwB _).2, ?_, ?_⟩
  · filter_upwards [hBn, hP] with z hz hPz hzX
    rw [hCE _ hz]
    exact hPz hzX
  · filter_upwards [hBn, hP, hiff σ X w d A ℓ N a δ q ha hδ hq hP hsep hQ, hW.mem_nhds hwW] with
      z hz hPz hsh hzW hzX hzδ
    have hr := hroot _ hz hzδ (ℓ z) (hPz hzX)
    have hs := hsh hzX hzδ W hW hzW
    exact ⟨hs.trans hr.1.symm, fun h h0 => hr.2.mp h0 (hs.mp h)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
