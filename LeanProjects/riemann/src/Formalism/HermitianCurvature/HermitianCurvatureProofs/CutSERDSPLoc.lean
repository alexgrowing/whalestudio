import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_locality : RDSPLoc := by
  intro k r Wp Wq _ _ _ _ _ _ Θ U X Y hU hXY g hgU hgV
  have h : ∀ x ∈ B.GV k r, x ∈ U → X x = Y x := fun x hx hxU => hXY x hxU hx
  exact ⟨Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_congr Θ hU h hgV hgU,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hU h g hgV hgU⟩

end Formalism.FourierDecayAlt.P.CutSE
