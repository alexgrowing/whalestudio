import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LinkSGap
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk

namespace Formalism.L2.SG.GapClosed

theorem gapEv_closed_of (𝒞 : FamClass) (hT : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) :
    Closed 𝒞 fun Fm _ => 𝒞 Fm → Formalism.L2.SG.LoopsTies.GapEv Fm := by
  obtain ⟨e, he, H⟩ := Formalism.L2.SG.ThmSOwn.gapRowT (𝒞 := 𝒞) (Formalism.L2.SG.ResidEvFree.residEv_closed_free 𝒞)
  refine ⟨e, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  exact ⟨K, fun Fm CH hc hL _ => hK Fm CH ⟨hc, hT Fm hc⟩ hL ⟨hc, hT Fm hc⟩⟩

end Formalism.L2.SG.GapClosed

end
