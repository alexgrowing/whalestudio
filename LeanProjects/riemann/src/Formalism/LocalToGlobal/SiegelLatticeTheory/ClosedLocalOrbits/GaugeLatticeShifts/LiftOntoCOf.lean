import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LatSpanLeSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram

namespace Formalism.L2.SG.Pf

theorem liftOntoC_of (hLI : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.SG.TermTieOf.LatIso D) : Formalism.L2.SG.Pf.SatGram.LiftOntoC :=
  fun D X Y u u' => Act.liftOnto (hLI D) (ratPt_holds D X) Y u u' (toTermRel_holds X u u' _ _)

end Formalism.L2.SG.Pf
