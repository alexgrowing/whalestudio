import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentOfIntegralModels
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OddDualWeyl

namespace Formalism.L2.G.RelativeIndexFlags

open Formalism.L2.G.Cmp

theorem oddFact_pf {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    OddFact (K := K) O m lam := oddDualWeyl O m lam

theorem weylLatticeDescent_holds : WeylLatticeDescent := weylLatticeDescent_of_integral_models fun m lam _ => oddFact_pf ℤ m lam

end Formalism.L2.G.RelativeIndexFlags
