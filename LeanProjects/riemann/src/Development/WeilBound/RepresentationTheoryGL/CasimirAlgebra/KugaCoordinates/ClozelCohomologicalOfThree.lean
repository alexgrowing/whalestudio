import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ClozelCohomologicalOfRest
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeHolds
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KugaAbsHolds
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CasimirBounds.CasBoundHolds
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CoefficientGluing.CoefGlueHolds

namespace PositivityTheory.Rg.Cz

theorem clozelCohomological_of_three (hw : WhitLie) (hkg : KugaGlue) (hco : Cochain) : GlobalTheory.Published.ClozelCohomological :=
  clozelCohomological_of_rest kType_holds GK.gkData_holds hw kugaAbs_holds hkg coefGlue_holds hco casBound_holds

end PositivityTheory.Rg.Cz
