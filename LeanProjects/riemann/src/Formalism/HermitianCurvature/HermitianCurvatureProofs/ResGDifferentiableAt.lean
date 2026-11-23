import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3

noncomputable section

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sf_resG {D : Set (Mx k r)} {F : Mx k r → E} (hF : SmoothLev k r 0 D F) (i : Fin (r + 1)) :
    SmoothFam k r i (Formalism.FourierDecayAlt.P.Qx6.UU (Formalism.FourierDecayAlt.P.Qx6.Dcell D i)) (resG k r i F) := by
  induction i using Fin.induction with
  | zero =>
    have e : resG k r 0 F = fun _ => F := by
      funext c g
      exact Formalism.FourierDecayAlt.P.Qx6.resG_zero F c g
    rw [e, Formalism.FourierDecayAlt.P.Qx6.Dcell_zero]
    exact Formalism.FourierDecayAlt.P.Qx6.sf_const_fam hF
  | succ l ih =>
    rw [Formalism.FourierDecayAlt.P.Qx6.resG_succ, Formalism.FourierDecayAlt.P.Qx6.Dcell_succ]
    exact Formalism.FourierDecayAlt.P.Qx6.sf_Res Formalism.FourierDecayAlt.P.weyl_level_element_properties l ih

end

end Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3
