import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem ssnRep_of_open2 (hPE : PRho.PRhoExists) (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  ssnRep_of_open hPE theta_facts_hold hMC hLN hPoly

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
