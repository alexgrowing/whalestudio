import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnDatumBd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChainPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem datum_bound_holds : DatumBd := datumBd_of_chain SSn.ChainPf.chain_bound_holds

theorem jABddKapQQ_of_leaves (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_typeProj datum_bound_holds hG hP

theorem jABddKapQQ_of_cut (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) (hNW : NrmWFacts) : JABddKapQQ :=
  jABddKapQQ_of_leaves hG (typeProj_of hPE hGL hDU hNW)

end Formalism.FourierDecayAlt.P.CutMP.JA
