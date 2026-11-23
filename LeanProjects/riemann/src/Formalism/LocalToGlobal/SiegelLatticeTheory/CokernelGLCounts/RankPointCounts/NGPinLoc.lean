import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns

namespace Formalism.L2.SG.NGPin

theorem locRootHaar_holds : LocRootHaar :=
  fun k r hk z z' h1 h2 h3 h4 p g₀ hg hZ => Formalism.L2.SG.Pf.RootHaarLoc.locRootHaar k r hk z z' h1 h2 h3 h4 p g₀ hg hZ

theorem placeHaar_holds : PlaceHaar := Formalism.L2.SG.RootPatterns.placeHaar_of_loc locRootHaar_holds

theorem stepPinExists : Formalism.L2.SG.NGAnalytic.StepPinExists := stepPinExists_of_place placeHaar_holds

end Formalism.L2.SG.NGPin
