import Formalism.ThetaLogCoordinates.SandwichModelDomains.SpreadSquare
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

theorem sandwichDomain_of (h : SandwichZ) (hA : AscentDomain) : SandwichDomain := by
  intro p _ r n hn ν hν l hl O _ _ hO
  exact ⟨hA p r n hn ν _ (h p r n hn ν hν l hl) O hO, weylLeDual O r n hn ν hν⟩

end Formalism.InvariantFactorPaths.INST
