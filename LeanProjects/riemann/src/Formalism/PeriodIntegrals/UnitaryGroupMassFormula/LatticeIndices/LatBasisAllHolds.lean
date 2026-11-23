import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion

noncomputable section

namespace MassDataIdxSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem latBasisAll_holds {D : D7} (X : HidaSetting D) (p : TypX X) : LatBasisAll X p := by
  apply latBasisAll_of_parts
  · intro θ hθ
    exact denom_holds (X := X) (p := p) (θ := θ) hθ
  · intro θ hθ
    exact approx_of (X := X) (p := p) (θ := θ) hθ (denseF_holds X p) (epsLat_holds X p θ)

theorem stRed_of_embP {D : D7} (X : HidaSetting D) (p : TypX X) (hE : EmbP X p) : StRed X p :=
  stRed_of_emb X p hE (latBasisAll_holds X p)

end MassDataIdxSteps
