import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreDone
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotK

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gauge_construction_holds : GCore := gCore_of_rotK rotation_K_invariance_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_SSnRep (hJ : JfSmoothDS) (h : JA.SSn.SSnRep) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_rotK hJ Gauge.GC.rotation_K_invariance_holds h

end Formalism.FourierDecayAlt.P.CutMP
