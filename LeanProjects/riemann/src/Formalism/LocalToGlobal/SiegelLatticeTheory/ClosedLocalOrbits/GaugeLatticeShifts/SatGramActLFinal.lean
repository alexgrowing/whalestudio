import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActL
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLChi

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.SatGramActL

theorem left_action_of_local_data (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D)
    (hGen : ∀ D : D7, Formalism.L2.SG.Saturated.GenIso (VS D) D.R.rS (gS D))
    (hIR : Formalism.L2.SG.Pf.SatGramRep.IotaRepC) (hAR : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC) (hCB : ChiNBiAll) :
    LeftActC' :=
  left_action_three_families hPD betaLift_holds (sMemLeft_holds hGen hPD) iotaLeft_holds (chiNLeft_holds hCB) ooLeft_holds
    fundConj_holds hIR hAR

end Formalism.L2.SG.Pf.SatGramActL
