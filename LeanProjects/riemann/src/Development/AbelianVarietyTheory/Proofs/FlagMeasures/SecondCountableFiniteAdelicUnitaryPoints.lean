import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem secondCountable_finiteAdelicPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf :=
  fun I => (adelic_topology I).2.2.1

end GlobalTheory.CongTop
