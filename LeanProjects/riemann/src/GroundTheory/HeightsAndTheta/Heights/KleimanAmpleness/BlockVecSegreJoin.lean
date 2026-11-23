import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

instance segreIdx.fintype {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    ∀ k, Fintype (Sum.elim (fun _ : Unit => ∀ k, ι k) ι k) := fun k => by
  cases k <;> infer_instance

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
