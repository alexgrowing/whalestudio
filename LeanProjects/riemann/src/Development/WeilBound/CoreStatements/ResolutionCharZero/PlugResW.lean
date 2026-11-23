import Mathlib
import Development.ResolutionOfSingularities.HasSimpleNormalCrossingsOfInStrictNormalCrossing
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromRes

namespace PositivityTheory.ResPlug.FromRes

theorem resW : PositivityTheory.ResPlug.ResW :=
  resW_of_functorialResolution FunctorialResolution.functorialResolutionCharZero.{0}

end PositivityTheory.ResPlug.FromRes
