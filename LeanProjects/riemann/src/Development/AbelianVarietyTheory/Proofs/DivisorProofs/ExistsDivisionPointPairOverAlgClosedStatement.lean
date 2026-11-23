import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisionPointPairOverAlgClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisionPoint_pair_over_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  first | exact @GlobalTheory.UCanon.exists_qk_over_cF | exact GlobalTheory.UCanon.exists_qk_over_cF | (intros; apply GlobalTheory.UCanon.exists_qk_over_cF <;> assumption)
