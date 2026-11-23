import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsDlogFirstChernClass
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InstFintypeHodgeBidegree

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Om

section
variable {K : Type} [Field K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

abbrev HodgeC (a j : ℕ) : Type := GlobalTheory.HodgeCoh.hodgeH q a j

variable {q} in

def pullC {p : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ X) (hu : u ≫ q = p) (a j : ℕ) : HodgeC q a j →ₗ[K] HodgeC p a j :=
  GlobalTheory.HodgeCoh.hodgePull hu a j

end

end CrystallineSemistableComparison.Om
