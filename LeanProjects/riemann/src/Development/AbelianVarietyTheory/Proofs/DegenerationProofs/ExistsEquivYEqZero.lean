import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem exists_equiv_y_eq_zero : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (pk : QkPt D.toPre F k) (z : D.toPre.X), pk.y = k • z → ∃ p' : QkPt D.toPre F k, p'.y = 0 ∧ QkPt.Equiv D.toPre F pk p' := by
  intro _ R _ _ _ I _ D F _ _ _ k pk z hz
  refine ⟨GlobalTheory.TorusExt.qkShift D.tau_bimult pk (-z), ?_, GlobalTheory.TorusExt.equiv_qkShift D.tau_bimult pk (-z)⟩
  show pk.y + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

end GlobalTheory.ZH
