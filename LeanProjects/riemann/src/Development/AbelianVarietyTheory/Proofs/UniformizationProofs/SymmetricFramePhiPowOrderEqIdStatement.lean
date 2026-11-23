import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricFramePhiPowOrderEqId
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.symmetricFrame_phi_pow_order_eq_id : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : Frm D.toPre F N p.g.b), TXFrame N p w → ∀ ss : Fin (N + 1) → Fam D.toPre F N, (∀ i : Fin N, PhiRel D.toPre F N p w (ss i.castSucc) (ss i.succ)) → ss (Fin.last N) = ss 0 := by
  first | exact @GlobalTheory.UT.PhiOrder.main | exact GlobalTheory.UT.PhiOrder.main | (intros; apply GlobalTheory.UT.PhiOrder.main <;> assumption)
