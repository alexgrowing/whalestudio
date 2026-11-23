import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtGenUniform
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenerationOfH1Vanishing.proof (hU : ClosedPtGenUniform.Statement) (hC : GenNearCover.Statement) :
    GenerationOfH1Vanishing.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨c₂, hc₂⟩ := hH M 𝓜 hfin hgr hV e
  obtain ⟨c₃, hc₃⟩ := hC S K ι V M 𝓜 (fun c => e + c • N) hS hgr hV
    (fun P hP _ => hU S K ι V N hS hH M 𝓜 hfin hgr hV e P hP)
  exact ⟨max c₂ c₃, fun c hc => ⟨hc₂ c (le_of_max_le_left hc), hc₃ c (le_of_max_le_right hc)⟩⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
