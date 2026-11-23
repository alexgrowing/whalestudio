import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFullFlagRestrictBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open IndefiniteRowSideFullHecke.NumbersDVR.Bundles IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagRestrict

theorem FullFlagRestriction.proof : FullFlagRestriction.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ B _ Q _ hQ hPQ
  obtain ⟨_, hQh, hQr⟩ := hQ
  refine ⟨mcIdeal_genPt Q hQh, resBundle B hPQ, rfl, fun fl => ?_⟩
  obtain ⟨fl', h1, h2⟩ := exists_resFlag hPQ hQr fl
  exact ⟨fl', h1, h2⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
