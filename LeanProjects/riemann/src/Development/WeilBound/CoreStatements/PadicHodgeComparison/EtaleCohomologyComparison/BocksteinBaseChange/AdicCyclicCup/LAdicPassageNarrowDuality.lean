import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PoincareDualityProjectivePoint
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

structure ZIn2 : Prop where
  nat : GlobalTheory.EtC.DivisorNaturality
  ring : GlobalTheory.EtC.DivisorRingCompatibility
  a9 : GlobalTheory.EtC.A9
  a11 : GlobalTheory.EtC.A11
  e4 : GlobalTheory.EtC.E4
  core : GlobalTheory.EtC.PoincareDualityProjectivePoint
  top : GlobalTheory.EtC.PointClassOrder
  bock : InBock
  root : InRoot
  sum : InSum

def LAdicPassageNarrowDuality : Prop := ZIn2 → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (G : Model l K → Prop),
  (∀ M, G M → M.Good) → CompM G → (∀ M, G M → ∀ d, M.Conn d → M.Geo) → EtSide G

end CrystallineSemistableComparison
